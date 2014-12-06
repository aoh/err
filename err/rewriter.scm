;;;
;;; Simple term rewriting proof searcher
;;;

;; todo - theorems and proofs do not yet tag types, so Ir etc don't usually match

(define-library (err rewriter)

   (import
      (owl base)
      (err util)
      (err pretty))

   (export 
      look-for-reduction)     ;; env A B → #false | (rewrite A <proof>) - leading to B

   (begin

      (define (maybe-clone-left term lhss tail)
         (if lhss 
            (fold (λ (tail carp) (cons (cons carp (cdr term)) tail)) (or tail null) lhss)
            tail))

      (define (maybe-clone-right term rhss tail)
         (if rhss 
            (fold (λ (tail cdrp) (cons (cons (car term) cdrp) tail)) (or tail null) rhss)
            tail))

      ;; term rule → #false | (term' ...) being all ways to contract term using rule
      (define (contractions term rule)
         (let ((termp (rule term)))
            (cond 
               ((pair? term)
                  (maybe-clone-left term (contractions (car term) rule)
                     (maybe-clone-right term (contractions (cdr term) rule)
                        (if termp (list termp) #false))))
               (termp
                  (list termp))
               (else #false))))

      (define (contract-leftmost term rule)
         (cond
            ((rule term)
               => (λ (termp) termp))
            ((not (pair? term))
               #false)
            ((contract-leftmost (car term) rule) =>
               (λ (lhs) (cons lhs (cdr term))))
            ((contract-leftmost (cdr term) rule) =>
               (λ (rhs) (cons (car term) rhs)))
            (else #false)))

      (define (contract-some rs term rule)
         ; (print "at contract-some for " term)
         (let ((opts (contractions term rule)))
            ; (print "opts are " opts)
            (if opts
               (rand-elem rs opts)
               (values rs #false))))

      ;; ((term1.rule1) .. (termn . #false)) → ((term2 . rule) ... (termn . rule_n-1))
      (define (push-rules lst)
         (let loop ((lst (cdr lst)) (rule (cdar lst)))
            (if (null? lst)
               null
               (cons
                  (cons (caar lst) rule)
                  (loop (cdr lst) (cdar lst))))))

      (define (find-match fs ts)
         (let loop ((fs fs)) ;; both fs and ts are reverse (ts thus on correct order)
            (cond
               ((null? fs)
                  #false)
               ((mem (λ (a b) (equal? (car a) (car b))) ts (car fs)) =>
                  (λ (ts)
                     (lets
                        ((forward (reverse fs))
                         (start-term (caar forward)) ;; first term is (term . #false)
                         (steps (cdr forward))
                         (backward (push-rules ts)) ;; drop the first, just push rule down
                         (all-steps (append steps backward)))
                        ;; set memberships (a[Ψ]) can be read as comments, but drop them anyway for readability
                        (tuple 'rewrite 
                           (drop-sets 
                              start-term)
                           (drop-sets
                              (map 
                                 (λ (pair) (cons (cdr pair) (car pair)))
                                 all-steps))))))
               (else
                  ; (print "Did not find " (car fs) " from " ts)
                  (loop (cdr fs))))))

      ;; rs ((term . last-rule-name) ...) rule name → rs #false | rs ((term' . rule-name) (term . last-rule-name) ...)

      (define (step rs lst rule rule-name)
         ; (print "stepping, rs " rs ", lst " lst)
         (lets ((rs next (contract-some rs (caar lst) rule)))
            (values rs
               (if next
                  ;; avoid rewriting to a term that already is in list
                  ;; TODO: not benchmarked if this makes sense
                  ;(if (first (λ (x) (equal? (car x) next)) lst #false)
                  ;   #false
                  ;   (cons (cons next rule-name) lst))
                  (cons (cons next rule-name) lst)
                  #false))))

      (define (definer name value)
         (λ (term)
            (cond
               ((eq? term name) value)
               ((equal? term value) name)
               (else #false))))

      ;; env ((term . rulename) ...) → env #false | env ((term' . name') (term . name) ...)
      ;; use a theorem or definition from env once to compute
      
      (define (reduce-once-with rs env terms)
         ;(print "reduce-once-with " terms)
         (lets
            ((rs defns (rand rs 4))
             (opts 
               (ff-fold
                  (λ (opts name value)
                     (cond
                        ((function? value) ;; rewriter
                           ;(print " - adding rewriter of " name)
                           (cons (cons name value) opts))
                        ((or (pair? value) (symbol? value))
                           ;(print " - adding definition of " name)
                           ;; maybe include definitions
                           (if (eq? defns 0)
                              (cons (cons 'definition (definer name value)) opts) ;; set the rule to 'definition'
                              opts))
                        (else opts)))
                  null env))
             (rs opts (random-permutation rs opts))) ;; try in random order (learned weights later)
            (let loop ((rs rs) (opts opts))
               (if (null? opts)
                  (values rs #false) ;; no theorem or definition applies
                  (lets ((rs termsp (step rs terms (cdar opts) (caar opts))))
                     (if termsp
                        (begin
                           ;(print "Used " (car terms))
                           (values rs termsp))
                        (loop rs (cdr opts))))))))

      (define (print-steps steps)
         (print "Proof trail: " steps)
         (for-each
            (λ (step)
               (print "  = " (render-cexp (car step)) " by " (cdr step)))
            steps))

      (define (look-for-reduction env bindings from to)

         (define eq-check-bits #b1111)

         (define max-steps 30)
         (define max-tries 20)

         (define rs (seed->rands (time-ms))) ;; are you feeling lucky?
         ;(define rs (seed->rands 42)) ;; let's be deterministic

         (define (try fs ts rs n)
            ;(print "----------------8<------------------")
            ;(print "From: steps " n)
            ;(print-steps fs)
            ;(print "To:")
            ;(print-steps ts)
            ;(print "")
            (cond
               ((eq? 0 n)
                  (values rs #false))
               ((eq? 0 (band n eq-check-bits))
                  ;(print "*** looking for match ***")
                  (let ((res (find-match fs ts)))
                     (if res
                        (values rs res)
                        (try fs ts rs (- n 1)))))
               (else
                  (lets
                     ((rs fsp (reduce-once-with rs env fs))
                      (rs tsp (reduce-once-with rs env ts)))
                     (cond
                        (fsp
                           (try fsp (if tsp tsp ts) rs (- n 1)))
                        (tsp
                           (try fs tsp rs (- n 1)))
                        ((find-match fs ts)
                           => (λ (soln) (values rs soln)))
                        (else
                           (values rs #false)))))))

         (lets
            ((from to (apply-bindings bindings from to))
             (froms (list (cons from #false)))
             (tos (list (cons to #false))))
            ;(print (render-cexp from) " + " bindings " = " (render-cexp (apply-bindings bindings from)))
            (let loop ((rs rs) (len 4) (tries 0))
               ;(print-to stderr " - len " len)
               (if (> len max-steps)
                  (if (> tries max-tries)
                     #false
                     (loop rs 4 (+ tries 1)))
                  (lets
                     ((rs solnp (try froms tos rs len))
                      (rs stepp (rand rs len)))
                     (cond
                        (solnp solnp)
                        ((eq? stepp 0)
                           (loop rs (+ len 1) tries))
                        (else
                           (loop rs len tries))))))))

))






