#!/usr/bin/ol -r

; err - equational reduction reasoner
; this is an experiment on how minimal logic would be useful for expressing computations and also 
; reasoning about them, both automatically and by proof checking.

(define-library (err main)
   
   (import 
      (owl base)
      (owl args)    ;; command line argument handling
      (err check)   ;; proof checking
      (err prove)   ;; proof finding
      (err trace)   ;; verbosity message printer
      (err parse))  ;; theory parsing
   
   (export 
      main)         ;; (arg ...) → int
 
   (begin

      ;; term → #false | term' - rewrite (S A B C)→(A C (B C)) or (K A B)→A if the term matches

      (define (*-reduce x)
         (if (pair? x)
            (lets ((x c x))
               (if (pair? x)
                  (lets ((x b x))
                     (if (pair? x)
                        (lets ((x a x))
                           (if (eq? x 'S)
                              (cons (cons a c) (cons b c))
                              #false)) 
                        (if (eq? x 'K) ;; ((K . b) . c)
                           b
                           #false)))
                  #false))
            #false))

      ;; initial env
      (define tabula-combinatory-logica
         (list->ff
            (list
               ;; primitive core things
               (cons 'Ψ "cterm")
               ;(cons 'S     'S) ;; combinators map to self in env
               ;(cons 'K     'K) ;; -||-
               (cons 'reduce *-reduce)
               (cons 'η+    'η+) ;; proof by extensionality, Q ⊢ A = B ⇒ Q ⊢ (A X) = (B X) where X ∊ Ψ and X∉Free[A,B]
               (cons 'η-    'η-) ;; reverse extension,   Q ⊢ (A X) = (B X) ⇒ Q ⊢ A = B where -||-
               )))

      (define usage-text "usage: err [args] [file]")

      (define command-line-rules
         (cl-rules
            `((help "-h" "--help" comment "show this thing")
              (prove "-p" "--prove" comment "try to complete proofs")
              (verbose "-v" "--verbose" comment "increase verbosity" plural)
              (cheat #false "--cheat" comment "enable 'by cheat' in proof checking"))))

      ;; todo: not checked for collisions
      (define initial-symbols
         (list 'S 'K 'Ψ 'ℕ 'reduce 'IH 'cheat 'η+ 'η- 'definition 'succ 'add 'mul 'zero 'one 'sub))

      (define (initialize-environment env dict args)
         (cond
            ((getf dict 'cheat)
               (initialize-environment 
                  (put env 'cheat 'cheat) ;; enable cheat -rule
                  (del dict 'cheat)
                  args))
            (else 
               env)))

      (define (start-err dict args)
         (cond
            ((getf dict 'help)
               (print usage-text)
               (print-rules command-line-rules)
               0)
            (else
               (lets
                  ((paths (if (null? args) (list "-") args))
                   (ss terms (err-loads initial-symbols paths))
                   (env (initialize-environment tabula-combinatory-logica dict args)))
                  (start-tracer (get dict 'verbosity 0))
                  (cond
                     ((not terms)
                        1)
                     ((getf dict 'prove)
                        ;; theory output -> ok should be comment
                        (if (prove-all env terms)
                           (begin (print "\n[OK]") 0)
                           (begin (print "\nFAIL") 1)))
                     (else
                        (if (check-exps env terms)
                           (begin (print "\nOK") 0)
                           (begin (print "\nFAIL") 1))))))))

      (define (main args)
         (process-arguments (cdr args)
            command-line-rules usage-text start-err))))

(import (err main))

main ;; args → int


