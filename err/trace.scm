(define-library (err trace)

   (import 
      (owl base)
      (err pretty))

   (export
      start-tracer      ;; verbosity → _
      debug)            ;; thing ... → _

   (begin

      (define (sink)
         (wait-mail)
         (sink))

      (define (tracer verbosity)
         (let ((mail (wait-mail)))
            (print-to stderr "[TRACE " (ref mail 2) "]")
            (tracer verbosity)))

      (define (start-tracer verbosity)
         (fork-server 'trace
            (if (eq? verbosity 0)
               sink
               (λ () (tracer verbosity)))))
      
      (define (debug . msgs)
         (mail 'trace
            (cons 2 msgs)))))


