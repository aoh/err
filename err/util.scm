;; shared utilities (potentially dangerous - some shared between checking and proof search)

(define-library (err util)

   (import
      (owl base)
      (err pretty))

   (export
      add-theorem
      extend-env
      replace-one
      replace
      well-founded?
      base-case?
      drop-sets
      apply-bindings    ;; bindings term1 term2 → term1' term2', with eq?-matching replaced variables
      apply-env)

   (begin

      ;; s/#(term set)/term/g
      (define (drop-sets term)
         (cond
            ((pair? term)
               (cons (drop-sets (car term))
                     (drop-sets (cdr term))))
            ((tuple? term)
               ;; take just term/variable
               (ref term 1))
            (else term)))

      (define (base-case? term set-name)
         (cond
            ((pair? term)
               (and
                  (base-case? (car term) set-name)
                  (base-case? (cdr term) set-name)))
            ((tuple? term)
               (not (eq? set-name (ref term 2))))
            (else #true)))

      ;; is there a suitable base case?
      (define (well-founded? cases set-name)
         (first (λ (case) (base-case? case set-name)) cases #false))

      ; B = ((S . (K . S)) . K)
      (define b '((S . (K . S)) . K))
      (define i '((S . K) . K))
      (define cl-succ `(S . ,b))
      (define cl-add `((,b . S) . (,b . ,b)))
      (define cl-mul b)

      (define (number-var? x)
         (and (tuple? x) (eq? (ref x 2) 'ℕ)))

      (define (num-app-of-1 num? x term) ;; (term . var)?
         (and (pair? term)
            (equal? (car term) x)
            (num? (cdr term))))

      (define (num-app-of-2 num? x term) ;; ((term . var) . var)?
         (and (pair? term)
            (pair? (car term))
            (equal? (caar term) x)
            (num? (cdar term))
            (num? (cdr term))))

      ;; temp
      (define (numberish? term)
         ;(print "numberish? " (render-cexp term))
         (or
            (equal? term `(K . ,i)) ;; (K I) = zero
            (equal? term i) ;; I = one
            (equal? term 'zero)
            (equal? term 'one)
            (number-var? term)
            (num-app-of-1 numberish? cl-succ term)
            (num-app-of-1 numberish? 'succ term)
            (num-app-of-2 numberish? cl-mul term)
            (num-app-of-2 numberish? 'mul term)
            (num-app-of-2 numberish? cl-add term)
            (num-app-of-2 numberish? 'add term)
            (num-app-of-2 numberish? 'sub term)))

      (define (rewrite term env)
         (cond
            ((pair? term)
               (cons
                  (rewrite (car term) env)
                  (rewrite (cdr term) env)))
            ((tuple? term)
               (get env term term)) ; <- expected dragons about here
            (else
               term)))

      ;; eq?-preserving search and replace
      (define (replace term ff)
         (cond
            ((getf ff term) =>
               (λ (x) x))
            ((pair? term)
               (lets
                  ((l (replace (car term) ff))
                   (r (replace (cdr term) ff)))
                  (if (and (eq? l (car term)) (eq? r (cdr term)))
                     ;; no changes?
                     term
                     (cons l r))))
            ((tuple? term)
               (let ((new (list->tuple (map (λ (x) (replace x ff)) (tuple->list term)))))
                  (if (equal? new term)
                     term ;; preserve eq?
                     new)))
            (else
               term)))

      (define (replace-one term thing value)
         (replace term (put #empty thing value)))

      (define (apply-env env term)
         (call/cc
            (λ (exit)
               (define (walk term)
                  (cond
                     ((pair? term)
                        (cons (walk (car term))
                              (walk (cdr term))))
                     ((symbol? term)
                        (let ((val (getf env term)))
                           (or val
                              (begin
                                 ;(print "Unbound value " term ", likely ok for now.")
                                 term)))) ;; allowed in proof cases, since it will be bound after match
                     ((tuple? term)
                        (tuple-case term
                           ((case term proof)
                              (lets
                                 ((term (apply-env env term))
                                  (proof (apply-env env proof)))
                                 (tuple 'case term proof)))
                           ((rewrite term steps)
                              (lets
                                 ((steps (apply-env env steps))
                                  (term (apply-env env term)))
                                 (tuple 'rewrite term steps)))
                           (else
                              ;(print " ************** WHAT TUPLE IN APPLY TERM " term " ***************")
                              term)))
                     (else term)))
               (walk term))))

      ;; WARNING: eq? unique bindings are added, so do this only once
      (define (extend-env env bindings)
         ;(print "Adding bindings " bindings)
         (fold
            (λ (env binding)
               (if (getf env (car binding))
                  (print "WARNING: binding of " (car binding) " shadows old one."))
               (put env (car binding)
                  (tuple (car binding) (cdr binding)))) ;; #(A type) = variable
            env bindings))


      (define (match pat term env)
         ;(print "MATCH pattern " (render-cexp pat) " against " (render-cexp term) " in " env)
         (cond
            ((not env) #false)
            ((eq? pat term) env)
            ((tuple? pat)
               (let ((type (ref pat 2)))
                  (cond
                     ((eq? type 'Ψ)
                        ;; primitive class of all CL terms matches anything
                        (put env pat term))
                     ((and (tuple? term) (eq? (ref term 2) type))
                        ;; matching variables
                        (put env pat term))
                     ((eq? type 'ℕ)
                        (if (numberish? term)
                           (begin
                              ;(print "(dummy numberish matcher hit)")
                              (put env pat term))
                           (begin
                              ;(print "ℕ varialble not matching " term)
                              #false)))
                     (else
                        #false))))
            ((pair? term)
               (if (pair? pat)
                  (match (car pat) (car term)
                     (match (cdr pat) (cdr term) env))
                  (begin #false)))
            (else #false)))

      (define (make-rewriter term target)
         (λ (input)
            (let ((env (match term input #empty)))
               ;(if env  (print "will return " (rewrite target env)))
               (if env
                  (rewrite target env)
                  #false))))

      (define (apply-bindings bindings A B)
         (lets
            ((ff 
               (fold 
                  (λ (ff pair) (put ff (car pair) (tuple (car pair) (cdr pair))))
                  #empty bindings)))
            (values
               (replace A ff)
               (replace B ff))))

      (define (add-theorem env name from to)
         (put env name
            (make-rewriter from to)))

))
