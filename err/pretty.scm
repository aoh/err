;;;
;;; Proof prettyprinting
;;;

(define-library (err pretty)
   
   (import
      (owl base))

   (export
      err-prettyprint 
      render-cexp)

   (begin

      (define (display* . args)
         (for-each display args))

      ;; combinator expression → string
      (define (render-cexp term)
         (define (ren term)
            (cond
               ((pair? term)
                  (lets
                     ((l (ren (car term)))
                      (r (ren (cdr term))))
                     (if (eq? 40 (car l))
                        (append
                           (lets
                              ((l (cdr (reverse l)))
                               (l (if (eq? (car l) #\space) l (cons #\space l))))
                              (reverse l))
                           (append r (list 41)))
                        (append
                           (cons 40 l)
                           (cons #\space
                              (append r (list 41)))))))
               ((tuple? term)
                  (lets ((var type term))
                     (foldr render null
                        (list var "[" type "]"))))
               (else
                  (render term null))))
         (bytes->string
            (ren term)))

      ;; (l0 l1 .. ln-1 ln) X Y → (L0 X L1 X ... X ln-1 Y ln) , usually ", " " and "
      (define (interleaver l sep last-sep)
         (lets
            ((a l (uncons l #false))
             (b l (uncons l #false))
             (c l (uncons l #false)))
            (cond
               ((not a) null)
               ((not b) (list a))
               ((not c)
                  (ilist a last-sep b l))
               (else
                  (ilist a sep 
                     (interleaver (ilist b c l) sep last-sep))))))

      ;; (A B ... N) x → (A x B x .. x N)
      (define (interleave lst x)
         (interleaver lst x x))

      ;; ((variable . setid) ...) → string
      (define (render-bindings bindings)
         (if (null? bindings)
            ""
            (lets
               ((set (cdar bindings))
                (pred (λ (x) (eq? (cdr x) set)))
                (these (keep pred bindings))
                (others (remove pred bindings))
                (rest (render-bindings others)))
               (foldr string-append
                  (if (equal? rest "") rest (string-append " " rest))
                  (cons "∀"
                     (append
                        (interleave (map (o symbol->string car) these) ",")
                        (list "∊" (symbol->string set))))))))

      ;; ((variable . setid) ...) → string
      (define (render-set-bindings bindings)
         (let loop ((bindings bindings) (first? #true))
            (if (null? bindings)
               ""
               (lets
                  ((set (cdar bindings))
                   (pred (λ (x) (eq? (cdr x) set)))
                   (these (keep pred bindings))
                   (others (remove pred bindings))
                   (rest (loop others #false)))
                  (foldr string-append
                     rest
                     (cons (if first? " where " " and ")
                        (append
                           (interleaver (map (o symbol->string car) these) "," " and ")
                           (cons
                              (if (null? (cdr these))
                                 " is " 
                                 " are ")
                              (list "from " (symbol->string set))))))))))

      (define (indent i)
         (for-each (λ (x) (display " ")) (iota 0 1 i)))

      (define (prettyprint-proof proof i start?)
         (tuple-case proof
            ((rewrite term steps)
               (if start?
                  (begin
                     (indent i)
                     (print "proof")))
               (let ((i (+ i 3)))
                  (indent i)
                  (display (render-cexp term))
                  (let ((i (+ i 2)))
                     (for-each
                        (λ (step)
                           (print "")
                           (indent i)
                           (display* "= " (render-cexp (cdr step)) " by " (car step)))
                        steps)))) ;; leave out newline for potential QED
            ((induction var cases)
               (display* "proof by induction on " var)
               (let ((i (+ i 3)))
                  (map
                     (λ (case)
                        (tuple-case case
                           ((case pattern proof)
                              (print "")
                              (indent i)
                              (print "if " var " is " (render-cexp pattern) " then ")
                              (prettyprint-proof proof i #false))
                           (else
                              (print "BAD CASE IN PROOF"))))
                     cases)))
            (else
               (print "LOOK AT THE FUNNY MONKEY " proof))))

      (define (err-prettyprint term)
         (tuple-case term
            ((define name what)
               (print "define " name " as " (render-cexp what)))
            ((theorem name bindings from to proof)
               (print "theorem " name "\n   " (render-bindings bindings) " " (render-cexp from) " = " (render-cexp to))
               (prettyprint-proof proof 0 #true)
               (print " ▮"))
            ((set name opts bindings)
               (for-each display
                  (append 
                     (list "let set " name " have ")
                     (append
                        (interleaver (map render-cexp opts) ", " " and ")
                        (list (render-set-bindings bindings)))))
               (print ""))
            (else
               (print "HOW SHOULD I PRETTYPRINT " term))))))
  
