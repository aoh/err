(define-library (err check)
   
   (import 
      (owl base)
      (err util)
      (err pretty))           ;; err term prettyprinting (for proof output)
   
   (export 
      check-exps)

   (begin

      ;; check that proof starts with a/b and ends to b/a
      (define (check-proof-outcome proof a b)
         (tuple-case proof
            ((rewrite term steps)
               ;(print term)
               ;(print steps)
               (if
                  (or (and (equal? term a) (equal? (cdr (last steps #false)) b))
                      (and (equal? term b) (equal? (cdr (last steps #false)) a)))
                  #true
                  (begin
                     (print "I was expecting a proof that shows " a "=" b ", but got " term "=" (cdr (last steps #false)) ".")
                     #false)))
            ((induction id cases)
               ;; no, the outcome may be different in induction
               (if
                  (all
                     (λ (case)
                        (lets ((_ term proof case))
                           (check-proof-outcome
                              (tuple 'case term  ;; replace variable with pattern
                                 (replace-one proof id term))
                              (replace-one a id term) ;; update goals
                              (replace-one b id term))))
                     cases)
                  #true
                  (begin
                     (print "Outcome check for induction over " id " failed.")
                     #false)))
            ((case term proof)
               (check-proof-outcome proof a b))
            (else
               (print "BUG: Bad proof term: " proof)
               #false)))


      ;; check if rule (equivalence-preserving rewriter) can convert A into B by rewriting zero or one subterms

      (define (subterm-rewrite A rule B)
         (cond
            ((eq? A B)
               ;; same literal (later also same application term if using hash-consing)
               #true)
            ((equal? (rule A) B)
               ;; equality after one rewrite
               #true)
            ((and (pair? A) (pair? B))
               ;; subterm to rewrite could be deeper
               (cond
                  ((equal? (car A) (car B))
                     ;; possible difference only in right branch
                     (subterm-rewrite (cdr A) rule (cdr B)))
                  ((equal? (cdr A) (cdr B))
                     ;; difference only in left branch
                     (subterm-rewrite (car A) rule (car B)))
                  (else
                     ;; match here tried already, so both branches cannot differ
                     #false)))
            (else
               #false)))

      ;; is there a subterm in A or B that when contracted using only given rewriter yields (exactly) the other term 

      (define (match-using? A rule B)
         (or
            (subterm-rewrite A rule B)
            (subterm-rewrite B rule A)))

      (define (occurs? term var)
         (define (walk term)
            (cond
               ((eq? term var) #true)
               ((tuple? term)
                  ;; variable, subproof etc
                  (fold (λ (found thing) (or found (walk thing))) #false
                     (tuple->list term)))
               ((pair? term)
                  (or (walk (car term))
                      (walk (cdr term))))
               (else
                  #false)))
         (if (symbol? var)
            (walk term)
            (begin
               (print "BUG: occurs-check for non-symbol: " var)
               #false)))

     ;; A B → var ((#false . var) | (var . #false))

      (define (extension-variable term extended)
         (cond
            ((not (pair? extended))
               (values #false #false))
            ((equal? term (car extended))
               (if (symbol? (cdr extended))
                  (values (cdr extended) (cons #false (cdr extended))) ;; (? . var)
                  (values #false #false)))
            ((equal? term (cdr extended))
               (if (symbol? (car extended))
                  (values (car extended) (cons (car extended) #false))
                  (values #false #false)))
            (else
               (print "EXTENSION-VARIABLE: failed for " (render-cexp term))
               (print "                         other " (render-cexp extended))
               (values #false #false))))

      (define (decontract term move)
         (cond
            ((not (pair? term))
               #false)
            ((equal? (car term) (car move))
               (cdr term))
            ((equal? (cdr term) (cdr move))
               (car term))
            (else
               (print "Faild to perform contraction " move ".")
               #false)))

      (define (check-steps env exp steps count ext)
         (if (null? steps)
            (if (null? ext) ;; check that all extensions have been undone
               #true
               (begin
                  (print "Proof uses extensionality only on one side, lacking " ext)
                  #false))
            (lets
               ((next (car steps))
                (move term next))
               (print " - " (render-cexp exp) " => ")
               (print "   " (render-cexp term) " by " move ", pos " count)
               (print "")
               (let ((rule (if (function? move) move (getf env move))))
                  (cond
                     ((eq? move 'cheat)
                        (if (getf env rule) ;; is cheating enabled?
                           (begin
                              (print-to stderr "*** CHEATING ***")
                              (check-steps env term (cdr steps) (+ count 1) ext))
                           (begin
                              (print "Tried to prove 'by cheat' but --cheat not given.")
                              #false)))
                     ((eq? move 'definition)
                        ;; they should be equal because definitions have been pre-applied in proof checking
                        (if (equal? exp term)
                           (check-steps env term (cdr steps) (+ count 1) ext)
                           #false))
                     ((eq? move 'η+)
                        (lets ((var step (extension-variable exp term)))
                           (cond
                              ((not var)
                                 (print "Extension doesn't look good.")
                                 #false)
                              ((occurs? (cons exp ext) var)
                                 (print "Variable used in extension already occurs in term " (render-cexp exp) " or current extensions.")
                                 #false)
                              ((getf env var)
                                 (print "Variable used in extension already has some meaning associated to it. Choose another one.")
                                 #false)
                              (else
                                 (check-steps env term (cdr steps) (+ count 1) (cons step ext))))))
                     ((eq? move 'η-)
                        (cond
                           ((null? ext)
                              (print "Tried to contract but no extensions left.")
                              #false)
                           ((equal? term (decontract exp (car ext)))
                              (check-steps env term (cdr steps) (+ count 1) (cdr ext)))
                           (else
                              #false)))
                     ((not rule)
                        (print "Unknown rule: " move)
                        #false)
                     ((match-using? exp rule term)
                        (check-steps env term (cdr steps) (+ count 1) ext))
                     (else
                        (print "Failed to rewrite " (render-cexp exp) " to " (render-cexp term) " using " move ".")
                        #false))))))


      (define (parent-set thing)
         (if (tuple? thing)
            (ref thing 2)
            #false))

      (define (induction-case-match setname case term env rec)
         ;(print (list 'induction-case-match setname case term))
         (cond
            ((not env)
               (values #false #false))
            ((eq? case term)
               (values env rec))
            ((tuple? case) ;; variable in set definition, has type info
               (let ((type (ref case 2)))
                  (cond
                     ((eq? type setname)
                        ;; recursive set definition, match to symbol and save in rec
                        (if (symbol? term)
                           (let ((new-variable (tuple term type)))
                              (values (put env term new-variable) (cons new-variable rec)))
                           (begin
                              (print "XXX Nonsymbol " case " vs " term)
                              (values #false #false))))
                     ((eq? type 'Ψ)
                        ;; matches any term, but handling just symbol pattern for now
                        (if (symbol? term)
                           (let ((new-variable (tuple term 'Ψ)))
                              (values (put env term new-variable) rec))
                           (begin
                              (print "*** Not allowing Ψ of definition to match " term " for now.")
                              (values #false #false))))
                     (else
                        ;; FIXME - allows overwriting definitions, just testing
                        (print "XXX Not allowing non-induction/Ψ variables in set-based induction proofs yet - tried to match " case " to " term)
                        (values #false #false)))))
            ((pair? case)
               (if (pair? term)
                  (lets
                     ((env rec (induction-case-match setname (car case) (car term) env rec)))
                     (induction-case-match setname (cdr case) (cdr term) env rec))
                  (values #false #false)))
            (else
               (values #false #false))))


      ;; term (<case> ...) → <case> <instantiated-case> (<induction-var> ...)
      (define (choose-induction-case id proof-case defn-cases)
         (if (null? defn-cases)
            (values #false #false #false)
            (lets
               ((env rec
                  (induction-case-match id (car defn-cases) (ref proof-case 2)
                     #empty null)))
               (print " + " (render-cexp (car defn-cases)) " = " env)
               (if env
                  (begin
                     (print "Proof case " (ref proof-case 2) " matched definition of set " id)
                     (values (car defn-cases) env rec))
                  (choose-induction-case id proof-case (cdr defn-cases))))))

      (define (match-case-types env id cases)
         (lets ((defn (getf env (parent-set id))))
            (if (and defn (eq? (ref defn 1) 'set))
               (lets
                  ((defn-cases (ref defn 2))
                   (set-id (parent-set id))
                   (matched-cases ;; match proof terms against inductive definition of variable
                     (map
                        (λ (proof-case)
                           (print "Choosing induction match for " (render-cexp (ref proof-case 2)))
                           (lets
                              ((case inst ivars
                                 (choose-induction-case set-id proof-case defn-cases)))
                              (print "PROOF CASE " (ref proof-case 2) " BOUND TO " inst)
                              (tuple case inst ivars proof-case)))
                        cases))
                   (missing-cases ;; check if any definition cases are not taken care of
                     (keep
                        (λ (defn-case)
                           (not
                              (first
                                 (λ (matched) (eq? defn-case (ref matched 1)))
                                      matched-cases #false)))
                        defn-cases)))
                  (cond
                     ((not (null? missing-cases))
                        (if (null? (cdr missing-cases)) ;; just one missing
                           (print "Proof over variable belonging to " set-id " omits case " (car missing-cases) ".")
                           (print "Proof over variable belonging to " set-id " omits cases "
                              (map (λ (case) (ref case 2)) missing-cases) "."))
                        #false)
                     (else
                        ;; looks good
                        matched-cases)))
               (begin
                  (print "BUG: Case object is not a member of something that is a set.")
                  #false))))

      ;; check any proof node
      (define (check-proof env proof from to)
         ;(print "CHECKING PROOF " proof)
         (tuple-case proof
            ((induction id cases)
               (lets
                  ((id (apply-env env id))
                   (cases (apply-env env cases))
                   (cases (match-case-types env id cases)))
                  (if cases
                     (fold
                        (λ (ok? case)
                           (and ok?
                              (lets ((defn-case bindings ivars proof-case case))
                                 (if (null? ivars)
                                    (if (empty? bindings)
                                       (lets
                                          ((proof (ref proof-case 3))
                                           (proof (replace-one proof id defn-case)))
                                          (check-proof env proof from to))
                                       (let ((term (apply-env env defn-case)))
                                          (print " + DUMMY FAIL OF SIMPLE CASE WITH BINDINGS " bindings)
                                          #false))
                                    (if (null? (cdr ivars)) ;; one induction variable
                                       (lets
                                          ((ind-from (replace-one from id (car ivars)))
                                           (ind-to   (replace-one to   id (car ivars)))
                                           ;; add induction hypothesis
                                           (env (add-theorem env 'IH ind-from ind-to))
                                           ;; bind matched pattern to variable used in induction
                                           (ind-value
                                             (replace (ref proof-case 2) bindings))
                                           (env (put env id ind-value))
                                           (env (put env (ref (car ivars) 1) (car ivars)))
                                           (proof (ref proof-case 3))
                                           ;; change induction variable to case in proof
                                           (proof (replace-one proof id ind-value)))
                                          ;(print " + CHECKING INDUCTION BRANCH WITH HYPOTHESIS " (render-cexp ind-from) " → " (render-cexp ind-to))
                                          (check-proof env proof ind-from ind-to))
                                       (begin
                                          (print "NO MULTIPLE INDUCTION VARIABLE SUPPORT YET.")
                                          #false))))))
                        #true cases)
                     (begin
                        (print "Case analysis of " id " does not match set definition.")
                        #false))))
            ((rewrite term steps)
               (lets
                  ((term (apply-env env term))
                   (steps (map (λ (x) (cons (car x) (apply-env env (cdr x)))) steps)))
                  (print "Checking rewrite steps")
                  (check-steps env term steps 1 null)))
            (else
               (print "Bad proof term: " proof)
               #false)))

      ;; exp → ok? (env' | (errormsg ...))
      (define (err-eval env exp)
         ;(print "err-eval: " env ", " exp)
         (tuple-case exp
            ((define name what)
               (cond
                  ((getf env name)
                     (values #false
                        (list "tried to redefine " name)))
                  ((apply-env env what) =>
                     (λ (what)
                        (print "Adding definition " name " = " what " to env with " (keys env))
                        (values #true
                           (put env name what))))
                  (else
                     (values #false
                        (list "something wrong in " what)))))
            ((theorem name bindings from to proof)
               (print "Theorem " name ": " (render-cexp from) " = " (render-cexp to))
               (lets
                  ((envp (extend-env env bindings))
                   (from-bound (apply-env envp from)) ;; add definitions
                   (to-bound   (apply-env envp to)))
                  (cond
                     ((not (check-proof-outcome proof from to))
                        (values #false
                           (list "Proof mismatch with claim.")))
                     ((check-proof envp proof from-bound to-bound)
                        ;; print without rewritten definitions for readability
                        (print "Adding theorem " name ": " (render-cexp from) " = " (render-cexp to) ".")
                        (values #true
                           (add-theorem env name from-bound to-bound)))
                     (else
                        (values #false
                           (list "Your proof of " name " theorem does not convince me."))))))
            ((set name cases memberships)
               (lets
                  ((envp (extend-env env memberships))
                   (cases (apply-env envp cases)))
                  (if (well-founded? cases name)
                     (begin
                        (print "SET " name " HAS BASE CASE " (well-founded? cases name))
                        (for-each (λ (x) (print " - " x)) cases)
                        (print "TYPES: " memberships)
                        (values #true
                           (put env name (tuple 'set cases))))
                     (values #false
                        (list "No non-recursive base case found for " name ".")))))
            (else
               (values #false
                  (list "eval: what should i do with " exp)))))

      ;; failing fold
      ;; env exps → env' | #false + printed error message
      (define (err-check-list env exps)
         (if (null? exps)
            env
            (lets
               ((ok? envp (err-eval env (car exps))))
               (if ok?
                  (err-check-list envp (cdr exps))
                  (begin
                     (for-each (λ (x) (display-to stderr x))
                        (append envp (list "\n")))
                     #false)))))

      ;; note, symbols dropped
      (define (check-exps env exps)
         (if exps
            (err-check-list env exps)
            #false))

)) 

