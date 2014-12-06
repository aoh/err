(define-library (err parse)
   
   (import 

      (owl base)
      (owl parse)            ;; parsing DSL

      (only (owl intern)     ;; symbol interning helpers
         string->interned-symbol empty-symbol-tree put-symbol))
   
   (export 
      err-load
      err-loads)
 
   (begin

      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
      ;;; 
      ;;; Theory Syntax
      ;;; 

      (define get-id
         (let-parses
            ((chars 
               (get-kleene+ 
                  (get-rune-if 
                     (λ (x) 
                        (or
                           (and (<= #\a x) (<= x #\z))
                           (and (<= #\A x) (<= x #\Z))
                           (and (<= #\0 x) (<= x #\9))
                           (has? '(#\- #\+ #\_ #\?) x)
                           (> x 127) ;; misc unicode symbols
                           ))))))
            (list->string chars)))

      (define one-whitespace
         (get-either
            (get-rune-if
               (λ (x) (or (eq? x #\space) (eq? x #\newline))))
            (let-parses
               ((skip (get-imm #\[))
                (skip (get-greedy+ (get-byte-if (λ (x) (not (eq? x #\]))))))
                (skip (get-imm #\])))
               'whitespace)))
            
      (define opt-white
         (get-greedy* one-whitespace))

      (define white
         (get-greedy+ one-whitespace))

      (define (get-keyword str)
         (let-parses
            ((skip opt-white)
             (skip (get-word str str))
             (skip opt-white))
            str))

      (define (get-term self)
         (get-either
            get-id
            (let-parses
               ((skip (get-imm #\())
                (terms 
                  (get-kleene+
                     (let-parses
                        ((skip opt-white)
                         (this (self self)))
                        this)))
                (skip opt-white)
                (skip (get-imm #\))))
               (fold cons (car terms) (cdr terms)))))

      (define get-term 
         (let-parses
            ((skip opt-white)
             (val (get-term get-term)))
            val))

      ;; define <name> = <exp>

      (define get-definition
         (let-parses
            ((skip (get-word "define" #false))
             (skip white)
             (id get-id)
             (skip (get-keyword "as"))
             (value get-term))
            (tuple 'define id value)))

      (define get-set
         (let-parses
            ((skip opt-white)
             (skip (get-word "∀" #false))
             (vars
               (let-parses
                  ((skip opt-white)
                   (var get-id)     ;; ∀ A
                   (tail
                     (get-kleene*
                        (let-parses  ;; ∀ A [ , B,C,  D]
                           ((skip opt-white)
                            (skip (get-imm #\,))
                            (skip opt-white)
                            (id get-id))
                           id))))
                  (cons var tail)))
             (skip opt-white)
             (skip (get-word "∊" #false))
             (skip opt-white)
             (setname get-id))
            ;; -> ((var . setname) ...)
            (map
               (λ (var)
                  (cons var setname))
               vars)))

      (define get-equals
         (get-keyword "="))

      ;; (get-keywords "word1" "word2" ... return-value)
      (define-syntax get-keywords
         (syntax-rules ()
            ((get-keywords word ... value)
               (let-parses
                  ((skip (get-keyword word)) ...)
                  value))))
              
      ;; no rule given -> implicit "reduce"
      (define maybe-get-proof-step-name
         (get-either
            (let-parses
               ((skip (get-keyword "by")) ;; grabs trailing whitespace
                (name
                  (get-any-of
                     (get-keywords "induction" "hypothesis" "IH")
                     (get-keyword "IH")
                     get-id)))
               name)
            (get-epsilon "reduce"))) ;; default to reduction by (combinator) reduction


      ;; A = A' = A" = ... = B → #(rewrite A ((rule . A') ... (rule . B)))
      (define get-rewrite-proof
         (let-parses
            ((lhs get-term)
             (rhss
               (get-kleene+
                  (let-parses
                     ((skip get-equals)
                      (term get-term)
                      (rule maybe-get-proof-step-name))
                     (cons rule term)))))
            (tuple 'rewrite lhs rhss)))

      ;; (if <id> is <term> then <rewrite-proof>)+
      (define (get-induction-cases-of id)
         (get-kleene+
            (let-parses
               ((skip (get-keyword "if"))
                (skip (get-keyword id))
                (skip (get-keyword "is"))
                (case get-term)
                (skip (get-keyword "then"))
                (proof get-rewrite-proof))
               (tuple 'case case proof))))

      ;; by induction on <id> (if <id> is <term> then ...)+ → #(induction id (#(case <pattern> <proof>) ...))
      (define get-induction-proof
         (let-parses
            ((skip (get-keyword "by"))
             (skip (get-keyword "induction"))
             (skip (get-keyword "on"))
             (id get-id)
             (cases (get-induction-cases-of id)))
            (tuple 'induction id cases)))

      ;; (term (rule-used . term') ...)
      (define get-proof
         (let-parses
            ((skip (get-keyword "proof"))
             (proof 
               (get-any-of
                  get-induction-proof
                  get-rewrite-proof
                  ))
             (skip 
               (get-either 
                  (get-keyword "▮") 
                  (get-keyword "QED"))))
            proof))

      (define get-comma-and 
         (let-parses
            ((skip opt-white)
             (skip (get-either (get-imm #\,) (get-word "and" #false)))
             (skip opt-white))
            'comma))

      ;; <thing> [[, <thing>]* [,] and <thing]
      (define (get-list-of thing)
         (let-parses
            ((skip opt-white)
             (first thing)
             (rest
               (get-kleene*
                  (let-parses
                     ((skip get-comma-and)
                      (val thing))
                     val))))
            (cons first rest)))

      (define get-one-set-membership
         (let-parses
            ((things (get-list-of get-id))
             (skip (get-keyword (if (= (length things) 1) "is" "are")))
             (skip (get-keyword "from"))
             (skip opt-white)
             (parentset get-id))
            (map (λ (thing) (cons thing parentset)) things)))


      ;; <list> where [<idlist> is in <id>][, ....]
      (define get-set-memberships
         (let-parses
            ((skip (get-keyword "where"))
             (thingss
               (get-list-of
                  get-one-set-membership)))
            (foldr append null thingss)))

      ;; let set X have A[[, B]* [and C]] [where Q[[, W] [and E]] is/are from Z [, ...]]
      (define get-set-definition
         (let-parses
            ((skip (get-keyword "let"))
             (skip (get-keyword "set"))
             (name get-id)
             (skip (get-keyword "have"))
             (contents (get-list-of get-term))
             (memberships 
               (get-any-of
                  get-set-memberships
                  (get-epsilon null))))
            (tuple 'set name contents memberships)))

      ;; theorem <name> (∀<var>[,var]* ∊ set)* <exp> = <exp> proof term [= term' [by <theorem|lemma>]]+ ▮
      (define get-theorem 
         (let-parses
            ((skip (get-word "theorem" #false))
             (skip white)
             (name get-id) ;; theorem <id>
             (skip white)
             (sets (get-kleene* get-set)) ;; theorem <id> ∀ A,b ∊ Foo ...
             (skip opt-white)
             (lhs get-term) ;; theorem ... A 
             (skip opt-white)
             (skip (get-imm #\=))
             (skip opt-white)
             (rhs get-term) ;; theorem ... A = B
             (proof 
               (get-either
                  get-proof
                  (get-epsilon #false)))) ;; no proof, ok in assistant mode
            ;; trying out first how much one could do with this restricted form
            (tuple 'theorem name 
               (foldr append null sets)
               lhs rhs proof)))

      (define get-exp
         (let-parses
            ((skip opt-white)
             (value
               (get-any-of
                  get-definition
                  get-theorem
                  get-set-definition
                  )))
            value))

      (define get-theory 
         (let-parses
            ((stuff (get-greedy+ get-exp))
             (skip opt-white))
            stuff))



      ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
      ;;;
      ;;; Symbol Interning (possibly later also hash consing)
      ;;;

      ;; ss exp → ss' exp' (sans strings)
      (define (intern ss exp)
         (cond
            ((pair? exp)
               (lets
                  ((l r exp)
                   (ss l (intern ss l))
                   (ss r (intern ss r)))
                  (values ss (cons l r))))
            ((symbol? exp) 
               (values ss exp))
            ((tuple? exp)
               (lets
                  ((ss exp (intern ss (tuple->list exp))))
                  (values ss (list->tuple exp))))
            ((null? exp)
               (values ss exp))
            ((string? exp)
               (string->interned-symbol ss exp))
            ((eq? exp #false) ;; ok in partial proofs
               (values ss exp))
            (else
               (print "intern: what is " exp "?")
               (values #false #false)))) ;; <- boom

      (define (intern-all ss terms)
         (if (null? terms)
            (values ss terms)
            (lets 
               ((ss tl (intern-all ss (cdr terms)))
                (ss hd (intern     ss (car terms))))
               (values ss (cons hd tl)))))
       
      (define (err-load ss path)
         (let ((data (file->vector path)))
            (if data
               (let ((exps (try-parse get-theory (vec-iter data) path "bad theory: " #false)))
                  (cond
                     ((list? exps)
                        (intern-all ss exps))
                     ((not exps)
                        (values ss exps))
                     (else
                        (print-to stderr "err-load: bug: didn't get a term list or boolean from parser.")
                        (values ss #false))))
               (begin
                  (print-to stderr "Cannot open " path)
                  (values ss #false)))))
    
      ;; ss (path ..) → ss' (exp ...)|#false
      (define (err-loads syms paths)
         (define (load ss paths)
            (if (null? paths)
               (values ss null)
               (lets 
                  ((ss these (err-load ss (car paths))))
                  (if these
                     (lets ((ss rest (load ss (cdr paths))))
                        (if rest
                           (values ss (append these rest))
                           (values ss #false)))
                     (values ss #false)))))
         (load
            (fold put-symbol empty-symbol-tree syms)
            paths))))


