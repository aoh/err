
;;; proof searcher entry

(define-library (err prove)

   (import
      (owl base)
      (err util)
      (err pretty)
      (err trace)
      (err rewriter))

   (export
      prove-all)

   (begin

      (define (theorems-only env)
         (ff-fold
            (λ (env key value)
               (if (function? value)
                  (put env key value)
                  env))
            #empty env))

      (define (fresh-things env)
         (lets
            ((l (ff->list env))
             (l (sort (λ (a b) (lesser? (cdr a) (cdr b))) l)) ;; sort by value age (if heap object)
             (l (take (reverse l) 10)) ;; 10 newest things in env 
             (env (list->ff l)))
            env))

      ;; ((name . prof-fn) ...)
      (define leaf-techniques
         (list
            (cons 'rewriter 
               (λ (env bindings A B)
                  (let ((res (look-for-reduction env bindings A B)))
                     ;(print "[REWRITER returning " res "]")
                     res)))
            (cons 'fresh
               (λ (env bindings A B)
                  ;(print "[FRESH]")
                  (look-for-reduction
                     (fresh-things env)
                     bindings A B)))))

      (define fixed-eta-variables 
         '(unused α β γ δ ε))

      ;; add η+ and η- steps to both ends of proof
      (define (mark-eta proof sym)
         (tuple-case proof
            ((rewrite term moves)
               (tuple 'rewrite (car term)
                  (cons (cons 'η+ term) 
                     (append moves
                        (list (cons 'η- (cadr (last moves #false))))))))
            (else
               (error "mark-eta cannot handle " proof))))

      ;; pattern set → #(var set) | #false
      (define (induction-variable-of pat set)
         (cond
            ((tuple? pat)
               (if (eq? (ref pat 2) set)
                  pat
                  #false))
            ((pair? pat)
               (or 
                  (induction-variable-of (car pat) set)
                  (induction-variable-of (cdr pat) set)))
            (else 
               #false)))

      ;; binding is one of bindings. try to split proof around it.
      (define (try-induction-on binding prove env bindings A B done)
         ;(debug 'inducer 'trying binding 'on A '= B 'after done)
         ;(print 
         ;   "[inducer fired for " 
         ;      (render-cexp A) " = " (render-cexp B) 
         ;      ", variable " binding "]")
         (lets ((var setid binding))
            (tuple-case (getf env setid)
               ((set options)
                  (let loop ((options options) (cases null))
                     (if (null? options)
                        ;; all cases proved, yay \o/
                        (begin
                           ;(print "[INDUCTION COMPLETE]")
                           (tuple 'induction (car binding) cases))
                        (lets 
                           ((pattern (car options))
                            (bindings (keep (λ (x) (not (eq? x binding))) bindings))
                            (Ar (replace-one A var pattern))
                            (Br (replace-one B var pattern)))
                           (if (base-case? pattern setid)
                              (begin
                                 ; (print "[" var " = " pattern " is a base case of " setid ", trying to prove \n\t" Ar " = " Br "]")
                                 ; (print "[proving base case " var " = " pattern "]")
                                 (let ((proof (prove env bindings Ar Br done)))
                                    ;(print "[induction of " var " = " pattern " returned " proof "]")
                                    (if proof
                                       (loop (cdr options) 
                                          (cons (tuple 'case (drop-sets pattern) proof) cases))
                                       #false)))
                              (lets
                                 ((ivar (induction-variable-of pattern setid))
                                  (be (extend-env #empty bindings))
                                  (A  (apply-env be A))
                                  (B  (apply-env be B))
                                  (Ai (replace-one A var ivar))
                                  (Bi (replace-one B var ivar))
                                  (Ar (replace-one A var pattern))
                                  (Br (replace-one B var pattern))
                                  (env (add-theorem env 'IH Ai Bi)) ;; add induction hypothesis
                                  (proof (prove env bindings Ar Br done)))
                                 (if proof
                                    (loop (cdr options)
                                       (cons (tuple 'case (drop-sets pattern) proof) cases))
                                    (begin
                                       ;(print "[failed to prove case " var " = " pattern "]")
                                       #false))))))))
               (else
                  #false))))

      ;; todo: inducer, mitm-inducer (needs some partial term matching support for rewriter)
      (define branch-techniques
         (list
            (cons 'inducer
               (λ (prove env bindings A B done)
                  ;; let rewriters etc simple proof searchers to run for a while before 
                  ;; starting to look for induction proof
                  (if (not (equal? done '(inducer)))
                     ;; allow only one induction per proof
                     ;; TODO - later allow many and at any point after proof checker (and prettyprinter) can handle it
                     #false
                     (lets
                        ((opts
                           ;; not useful to do induction on arbitrary combinators
                           (keep (λ (x) (not (eq? (cdr x) 'Ψ))) bindings))
                         (delayed (zip cons (iota 0 1 (length opts)) opts))
                         (options
                           (map 
                              (λ (pair)
                                 (λ ()
                                    ;; exponentially growing delay between attempts
                                    (wait (* (expt 2 (+ 1 (car pair))) 1000))
                                    (try-induction-on (cdr pair) prove env bindings A B done)))
                              delayed)))
                        (if (null? options)
                           #false
                           (por* options))))))
            (cons 'eta
               (λ (prove env bindings A B done)
                  ;; todo, gensym instead
                  (let ((etas (length (keep (λ (x) (eq? x 'eta)) done))))
                     (if (< etas 4)
                        (let ((sym (list-ref fixed-eta-variables etas)))
                           ;(print "[trying eta " sym "]")
                           (wait (* (expt 2 etas) 100)) ;; wait a moment for other techniques to proceed between starting new etas
                           (let ((proof (prove env bindings (cons A sym) (cons B sym) done)))
                              (if proof
                                 (mark-eta proof sym)
                                 #false)))
                        (begin
                           ;(print "[not starting more etas]")
                           #false)))))

         ))

      ;; parallel proof search entry
      (define (prove env bindings from to done)
         ;(print "PROVE: bindings " bindings ", from " (render-cexp from) ", to " (render-cexp to) ", done " done)
         ;(print "PROVE: env " env)
         ;(debug 'trying 'to 'prove from '= to 'after done)
         (lets
            ((leaves 
               (map
                  (λ (node)
                     (lets ((name solver node))
                        (λ () 
                           (solver env bindings from to))))
                  leaf-techniques))
             (branches
               (map
                  (λ (node)
                     (λ () ((cdr node) prove env bindings from to (cons (car node) done))))
                  branch-techniques))
             (proofp 
               (por*
                  (append leaves
                     branches))))
            proofp))

      ;; → #true envp | #false (list of error strings etc)
      (define (err-prove env exp)
         ;(print "err-prove: " env ", " exp)
         (tuple-case exp
            ((define name what)
               (cond
                  ((getf env name)
                     (values #false
                        (list "tried to redefine " name)))
                  ;; TODO - no unbound check
                  (else
                     (err-prettyprint exp)
                     (values #true
                        (put env name what)))))
            ((theorem name bindings from to proof)
               (cond
                  (proof ;; not checking/filling it here temporarily
                     (err-prettyprint exp)
                     (lets
                        ((from-bound to-bound (apply-bindings bindings from to)))
                        (values #true 
                           (add-theorem env name from-bound to-bound))))
                  ((prove env bindings from to null) =>
                     (λ (proof)
                        (err-prettyprint (tuple 'theorem name bindings from to proof))
                        (lets
                           ((from-bound to-bound (apply-bindings bindings from to)))
                           (values #true
                              (add-theorem env name from-bound to-bound)))))
                  (else
                     (values #false
                        (list "I could not see why " (render-cexp from) " = " (render-cexp to))))))
            ((set name cases memberships)
               (lets
                  ((envp (extend-env #empty memberships)) ;; don't rewrite definitions
                   (cases (apply-env envp cases)))
                  (if (well-founded? cases name)
                     (begin
                        (err-prettyprint exp)
                        (values #true
                           (put env name (tuple 'set cases))))
                     (values #false
                        (list "No non-recursive base case found for " name ".")))))
            (else
               (values #false
                  (list "prove: what should i do with " exp)))))

      (define (prove-all env exps)
         (if (null? exps)
            env
            (lets
               ((ok? envp (err-prove env (car exps))))
               (print "")
               (if ok?
                  (prove-all envp (cdr exps))
                  (begin
                     (for-each (λ (x) (display-to stderr x))
                        (append envp (list "\n")))
                     #false)))))))
 
