;; Ryan Bailey & Josh Palamuttam
;; Assignment 13

;: Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

;(load "chez-init.ss") 
    
    ;-------------------+
    ;                   |
    ;    DATATYPES      |
    ;                   |
    ;-------------------+
    
    ; parsed expression
    
    (define-datatype expression expression?
        [var-exp
         (id symbol?)]
    
        [lambda-exp
         (id (list-of symbol?))
         (body (list-of expression?))]
    
        [lambda-no-paren-exp
         (id symbol?)
         (body (list-of expression?))]
    
        [lit-exp
         (id scheme-value?)]
    
        [if-exp
         (predicate expression?)
         (true-case expression?)
         (false-case expression?)]
    
        [if-no-else-exp
         (predicate expression?)
         (lone-case expression?)]
    
        [set!-exp
         (id expression?)
         (value expression?)]

        [set-car!-exp
            (id symbol?)
            (value expression?)]
        
        [set-cdr!-exp
            (id symbol?)
            (value expression?)]
    
        [let-exp
         (syms (list-of symbol?))
         (vals (list-of expression?))
         (body (list-of expression?))]
    
        [let*-exp
         (syms (list-of symbol?))
         (vals (list-of expression?))
         (body (list-of expression?))]
    
        [letrec-exp 
         (syms (list-of symbol?))
         (vals (list-of expression?))
         (body (list-of expression?))]
    
        [named-let-exp
         (proc-id symbol?)
         (syms (list-of symbol?))
         (vals (list-of expression?))
         (body (list-of expression?))]

        [app-exp
         (rator expression?)
         (rand (list-of expression?))])   
        
        
    
    ;; environment type definitions
    
    (define scheme-value?
      (lambda (x) #t))
    
    ; (define-datatype environment environment?
    ;   (empty-env-record)
    ;   (extended-env-record
    ;    (syms (list-of symbol?))
    ;    (vals (list-of scheme-value?))
    ;    (env environment?)))
    
    ; datatype for procedures.  At first there is only one
    ; kind of procedure, but more kinds will be added later.
    
    (define-datatype proc-val proc-val?
      [prim-proc
       (name symbol?)]
      [closure
        (ids (list-of symbol?))
        (bodies (list-of expression?))
        (env list?)])
         
        
    
    ;-------------------+
    ;                   |
    ;    PARSER         |
    ;                   |
    ;-------------------+
    
    
    ; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.
    
    
    (define 1st car)
    (define 2nd cadr)
    (define 3rd caddr)
    (define 4th cadddr)
  
    (define parse-exp        
      (lambda (datum)
        (cond
         [(symbol? datum) (var-exp datum)]
         [(boolean? datum) (lit-exp datum)]
         [(number? datum) (lit-exp datum)]
         [(string? datum) (lit-exp datum)]
         [(vector? datum) (lit-exp datum)]
         [(pair? datum)
          (cond
           [(eqv? (1st datum) 'quote)
                (lit-exp (2nd datum))]
           [(eqv? (1st datum) 'lambda)
              (if (or (pair? (2nd datum)) (null? (2nd datum)))
                  (if (< (length datum) 3)                    
                      (eopl:error 'parse-exp "Error  in parse-exp: lambda expression: incorrect length: ~s" datum)
                      (if (andmap (lambda (x) (symbol? x)) (2nd datum))
                          (lambda-exp (2nd datum) (map parse-exp (cddr datum)))
                          (eopl:error 'parse-exp "Error in parse-exp: lambda argument list: formals must be symbols: ~s" (2nd datum))))    
                  (if (< (length datum) 3)
                      (eopl:error 'parse-exp "Error in parse-exp: lambda expression: lambda expression missing body")
                      (lambda-no-paren-exp (2nd datum) (map parse-exp (cddr datum)))))]
  
           [(eqv? (1st datum) 'if)
              (if (or (< (length datum) 3) (> (length datum) 4))
                  (eopl:error 'parse-exp "Error in parse-exp: if expression: should have (only test, then , and else clauses)")      
                  (if (null? (cdddr datum))
                      (if-no-else-exp (parse-exp (2nd datum))
                                      (parse-exp (3rd datum)))
                      (if-exp (parse-exp (2nd datum))
                          (parse-exp (3rd datum))
                          (parse-exp (4th datum)))))]
          
           [(eqv? (1st datum) 'set!)
              (if (< (length datum) 3)
                  (eopl:error 'parse-exp "Error in parse-exp: set!: missing expression: ~s" datum)
                  (if (> (length datum) 3)
                      (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)
                      (set!-exp (parse-exp (2nd datum)) (parse-exp (3rd datum)))))]

            [(eqv? (1st datum) 'set-car!)
                (if (< (length datum) 3)
                    (eopl:error 'parse-exp "Error in parse-exp: set!: missing expression: ~s" datum)
                    (if (> (length datum) 3)
                        (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)
                        (set-car!-exp (2nd datum) (parse-exp (3rd datum)))))]

            [(eqv? (1st datum) 'set-cdr!)
                (if (< (length datum) 3)
                    (eopl:error 'parse-exp "Error in parse-exp: set!: missing expression: ~s" datum)
                    (if (> (length datum) 3)
                        (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)
                        (set-cdr!-exp (2nd datum) (parse-exp (3rd datum)))))]
  
           [(eqv? (1st datum) 'let)
                  (if (< (length datum) 3)
                      (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length: ~s" datum)
                      (if (and (not (pair? (2nd datum))) (not (null? (2nd datum)))) 
                          (eopl:error 'parse-exp "Error in parse-exp: let: declarations is not a list")
                          (if (not (proper-list? (2nd datum)))
                              (eopl:error 'parse-exp "Error in parse-exp decls: not a proper list: ~s" (2nd datum))
                              (if (not (andmap proper-list? (2nd datum)))
                                  (eopl:error 'parse-exp "Error in parse-exp: decls: not all proper lists: ~s" (2nd datum))
                                  (if (not (andmap (lambda (x) (equal? (length x) 2)) (2nd datum)))
                                      (eopl:error 'parse-exp "Error in parse-exp: decls: not all length 2: ~s" (2nd datum))
                                      (if (not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                                          (eopl:error 'parse-exp "Error in parse-exp: decls: first members must be symbols: ~s" (2nd datum))
                                          (if (or (pair? (2nd datum)) (null? (2nd datum)))
                                              (let-exp (map car (2nd datum)) (map (lambda (x) (parse-exp (cadr x))) (2nd datum)) (map parse-exp (cddr datum))) 
                                              (named-let-exp (2nd datum) (map (lambda (x) (car x)) (3rd datum))  (map (lambda (x) (parse-exp (cadr x))) (3rd datum)) (map parse-exp (cdddr datum))))))))))]
  
          [(eqv? (1st datum) 'let*)
              (if (< (length datum) 3)
                  (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length: ~s" datum)
                  (if (not (pair? (2nd datum))) 
                      (eopl:error 'parse-exp "Error in parse-exp: let*: declarations is not a list")
                      (if (not (proper-list? (2nd datum)))
                          (eopl:error 'parse-exp "Error in parse-exp decls: not a proper list: ~s" (2nd datum))
                          (if (not (andmap proper-list? (2nd datum)))
                              (eopl:error 'parse-exp "Error in parse-exp: decls: not all proper lists: ~s" (2nd datum))
                              (if (not (andmap (lambda (x) (equal? (length x) 2)) (2nd datum)))
                                  (eopl:error 'parse-exp "Error in parse-exp: decls: not all length 2: ~s" (2nd datum))
                                  (if (not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                                      (eopl:error 'parse-exp "Error in parse-exp: decls: first members must be symbols: ~s" (2nd datum))
                                      (let*-exp (map car (2nd datum)) (map (lambda (x) (parse-exp (cadr x))) (2nd datum)) (map parse-exp (cddr datum)))))))))]
  
          [(eqv? (1st datum) 'letrec)
              (if (< (length datum) 3)
              (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length: ~s" datum)
                  (if (not (pair? (2nd datum))) 
                  (eopl:error 'parse-exp "Error in parse-exp: letrec: declarations is not a list")
                      (if (not (proper-list? (2nd datum)))
                          (eopl:error 'parse-exp "Error in parse-exp decls: not a proper list: ~s" (2nd datum))
                          (if (not (andmap proper-list? (2nd datum)))
                              (eopl:error 'parse-exp "Error in parse-exp: decls: not all proper lists: ~s" (2nd datum))
                              (if (not (andmap (lambda (x) (equal? (length x) 2)) (2nd datum)))
                                  (eopl:error 'parse-exp "Error in parse-exp: decls: not all length 2: ~s" (2nd datum))
                                  (if (not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                                      (eopl:error 'parse-exp "Error in parse-exp: decls: first members must be symbols: ~s" (2nd datum))
                                      (letrec-exp (map car (2nd datum)) (map (lambda (x) (parse-exp (cadr x))) (2nd datum)) (map parse-exp (cddr datum)))))))))]                                
           [else (if (or (not (proper-list? datum)) (not (proper-list? (cdr datum))))
                    (eopl:error 'parse-exp "Error in parse-exp: application ~s is not a proper list" datum)
                    (app-exp (parse-exp (1st datum)) (map parse-exp (cdr datum))))])]
         [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

    (define proper-list?
        (lambda (ls)
            (cond
                [(null? ls) #t]
                [else (and (or (null? (cdr ls)) (pair? (cdr ls))) (proper-list? (cdr ls)))])))
      
    (define unparse-exp
        (lambda (exp)
            (cases expression exp
                [var-exp (id) id]
                [lambda-exp (id body)
                    (append (list 'lambda id)
                        (map unparse-exp body))]
                [lambda-no-paren-exp (id body)
                    (append (list 'lambda id)
                        (map unparse-exp body))]
                [lit-exp (id) id]
                [if-exp (predicate true-case false-case)
                    (list 'if (unparse-exp predicate) (unparse-exp true-case) (unparse-exp false-case))]
                [if-no-else-exp (predicate lone-case)
                    (list 'if (unparse-exp predicate) (unparse-exp lone-case))]
                [set!-exp (id value)
                    (list 'set! id (unparse-exp value))]
                [set-car!-exp (id value)
                    (list 'set-car! id (unparse-exp value))]
                [set-cdr!-exp (id value)
                    (list 'set-cdr! id (unparse-exp value))]
                [let-exp (syms vals body)
                    (append '(let) (join syms (map unparse-exp vals)) (map unparse-exp body))]
                [let*-exp (syms vals body)
                    (append '(let*) (join syms (map unparse-exp vals)) (map unparse-exp body))]
                [letrec-exp (syms vals body)
                    (append '(letrec) (join syms (map unparse-exp vals)) (map unparse-exp body))]
                [named-let-exp (proc-id syms vals body)
                    (append '(let proc-id) (join syms (map unparse-exp vals)) (map unparse-exp body))]
                
                [app-exp (rator rand)
                    (cons (unparse-exp rator)
                          (map unparse-exp rand))
                ])))

    (define (join L1 L2)
        (cond 
            [(null? L1) '()]
            [else (cons (list (car L1) (car L2)) (join (cdr L1) (cdr L2)))]))
    
    
    
    
    
    
    
    
    ;-------------------+
    ;                   |
    ;   ENVIRONMENTS    |
    ;                   |
    ;-------------------+
    
    
    
    
    
    ; Environment definitions for CSSE 304 Scheme interpreter.  
    ; Based on EoPL sections 2.2 and 2.3
    
    (define empty-env
      (lambda ()
        '()))
    
    (define extend-env
      (lambda (syms vals env)
        (cons (cons syms (list->vector vals))
               env)))
    
    ; (define list-find-position
    ;   (lambda (sym los)
    ;     (list-index (lambda (xsym) (eqv? sym xsym)) los)))
    
    ; (define list-index
    ;   (lambda (pred ls)
    ;     (cond
    ;      ((null? ls) #f)
    ;      ((pred (car ls)) 0)
    ;      (else (let ((list-index-r (list-index pred (cdr ls))))
    ;          (if (number? list-index-r)
    ;          (+ 1 list-index-r)
    ;          #f))))))

    (define rib-find-position 
        (lambda (sym syms)
            (if (member sym syms)
                (let recursion ([sym sym] [syms syms])
                    (cond 
                        [(eq? sym (car syms)) 0]
                        [else (+ 1 (rib-find-position sym (cdr syms)))]))
                #f)))
    
    (define apply-env 
        (lambda (env sym succeed fail)
            (if (null? env)
                (fail)                                  ;; Fail, the sym was not found
                (begin
                    (let ([syms (caar env)]
                      [vals (cdar env)]
                      [env (cdr env)])
                  (let ([pos (rib-find-position sym syms)])
                    (if (number? pos)
                      (succeed (vector-ref vals pos))                   ;; Succeed, we found the sym
                      (apply-env env sym succeed fail))))))))
                


    ; (define apply-env
    ;   (lambda (env sym succeed fail) ; succeed and fail are "callback procedures, 
    ;     (cases environment env       ;  succeed is applied if sym is found, otherwise 
    ;       [empty-env-record ()       ;  fail is applied.
    ;         (fail)]
    ;       [extended-env-record (syms vals env)
    ;         (let ((pos (list-find-position sym syms)))
    ;             (if (number? pos)
    ;                 (succeed (list-ref vals pos))
    ;                 (apply-env env sym succeed fail)))])))    
     
    
    
    ;-----------------------+
    ;                       |
    ;   SYNTAX EXPANSION    |
    ;                       |
    ;-----------------------+
    
    
    
    ; To be added later
    
    
    
    
    
    
    
    
    
    ;-------------------+
    ;                   |
    ;   INTERPRETER    |
    ;                   |
    ;-------------------+
    
    
    
    ; top-level-eval evaluates a form in the global environment
    
    (define top-level-eval 
      (lambda (form)
        ; later we may add things that are not expressions.
        (eval-exp form
                (empty-env))))
    

    (define identity-proc
        (lambda (x) x)) 
            
    (define common-fail
        (lambda ()
            (eopl:error 'common_error "Error")))
    ; eval-exp is the main component of the interpreter
    

    (trace-define eval-exp  
      (lambda (exp env)
        (cases expression exp
          [lit-exp (datum) datum]
          [var-exp (id)
            (apply-env env id                       ; look up its value.
                identity-proc                       ; identity procedure if it is in the environment 
                    (lambda ()                      ; Fail case now applies the global environment
                        (apply-env global-env id 
                            identity-proc               ; Same identity on success
                            (lambda ()                  ; procedure to call if it is not in env
                                (eopl:error 'apply-env 
                                    "variable not found in environment: ~s"
                                    id)))))] 
          [lambda-exp (id body)
            (closure id body env)]
          [lambda-no-paren-exp (id body) 1]
          [let-exp (syms vals body)
            (let ([extended-env
                    (extend-env syms
                                (map (lambda (x) (eval-exp x env)) vals)
                                env)])
                    (eval-bodies body extended-env))]
          [let*-exp (syms vals body) 1]
          [letrec-exp (syms vals body) 1]
          [named-let-exp (proc-id syms vals body) 1]
          [if-exp (predicate true-case false-case) 
            (if (eval-exp predicate env)
                (eval-exp true-case env)
                (eval-exp false-case env))]
          [if-no-else-exp (predicate lone-case) 1]
          [set!-exp (id value) (apply-proc 'set! (list (apply-env env id identity-proc (lambda () 'apply-env "variable not found in environment: ~s" id))) (eval-exp value env))]
          [set-car!-exp (id value)
                (apply-prim-proc 'set-car! (list (apply-env env id identity-proc common-fail) (apply (lambda (x) (eval-exp x env)) (list value))))]
          [set-cdr!-exp (id value)
                (apply-prim-proc 'set-cdr! (list (apply-env env id identity-proc common-fail) (apply (lambda (x) (eval-exp x env)) (list value))))]
          [app-exp (rator rands)
            (let ([proc-value (eval-exp rator env)]
                  [args (eval-rands rands env)])
              (apply-proc proc-value args))]
        [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))
    
    ; evaluate the list of operands, putting results into a list
    
    (define eval-rands
      (lambda (rands env)
        (map (lambda (e) (eval-exp e env)) rands)))

    (trace-define eval-bodies
        (lambda (bodies env)
            (if (null? (cdr bodies))
                (eval-exp (car bodies) env)
                (begin  
                    (eval-exp (car bodies) env)
                    (eval-bodies (cdr bodies) env)))))
    
    ;  Apply a procedure to its arguments.
    ;  At this point, we only have primitive procedures.  
    ;  User-defined procedures will be added later.
    
    (define apply-proc  
      (lambda (proc-value args)
        (cases proc-val proc-value
          [prim-proc (op) (apply-prim-proc op args)]
                ; You will add other cases
          [closure (ids bodies env) 
            (let ([extended-env (extend-env ids args env)])
                (eval-bodies bodies extended-env))]
          [else (eopl:error 'apply-proc
                       "Attempt to apply bad procedure: ~s" 
                        proc-value)])))
    
    (define *prim-proc-names* '(+ - * / add1 sub1 cons = list car cdr caar cddr cadr cdar cadar
                                not zero? >= > < <= null? equal? eq? pair? number? symbol? 
                                list->vector list? vector->list vector? procedure? length set-car! set-cdr!))
    
    (define global-env         ; for now, our initial global environment only contains 
      (extend-env            ; procedure names.  Recall that an environment associates
         *prim-proc-names*   ;  a value (not an expression) with an identifier.
         (map prim-proc      
              *prim-proc-names*)
         (empty-env)))
    
    ; Usually an interpreter must define each 
    ; built-in procedure individually.  We are "cheating" a little bit.
    
    (define apply-prim-proc  
      (lambda (prim-proc args)
        (case prim-proc
          [(+) (+ (1st args) (apply + (cdr args)))]
          [(-) (apply - args)]
          [(*) (* (1st args) (apply * (cdr args)))]
          [(/) (/ (1st args) (2nd args))]
          [(add1) (+ (1st args) 1)]
          [(sub1) (- (1st args) 1)]
          [(cons) (cons (1st args) (2nd args))]
          [(set-car!) (begin (let ([temp (1st args)])
                                 (set-car! temp (2nd args)) 
                                    temp))] 
          [(set-cdr!) (begin (let ([temp (1st args)])
                                (set-cdr! temp (2nd args))
                                    temp))]
          [(=) (= (1st args) (2nd args))]
          [(>=) (>= (1st args) (2nd args))]
          [(>) (> (1st args) (2nd args))]
          [(<) (< (1st args) (2nd args))]
          [(<=) (<= (1st args) (2nd args))]
          [(vector->list) (vector->list (1st args))]
          [(list->vector) (list->vector (1st args))]
          [(vector?) (vector? (1st args))]
          [(null?) (null? (1st args))]
          [(pair?) (pair? (1st args))]
          [(number?) (number? (1st args))]
          [(symbol?) (symbol? (1st args))]
          [(procedure?) (proc-val? (1st args))]
          [(not) (not (1st args))]
          [(eq?) (eq? (1st args) (2nd args))]
          [(equal?) (equal? (1st args) (2nd args))]
          [(zero?) (zero? (1st args))]
          [(list?) (list? (1st args))]
          [(length) (length (1st args))]
          [(list) args]
          [(car) (car (1st args))]
          [(cdr) (cdr (1st args))]
          [(caar) (caar (1st args))]
          [(cddr) (cddr (1st args))]
          [(cadr) (cadr (1st args))]
          [(cdar) (cdar (1st args))]
          [(cadar) (cadar (1st args))]
          [else (error 'apply-prim-proc 
                "Bad primitive procedure name: ~s" 
                prim-proc)])))
    
    (define rep      ; "read-eval-print" loop.
      (lambda ()
        (display "--> ")
        ;; notice that we don't save changes to the environment...
        (let ([answer (top-level-eval (parse-exp (read)))])
          ;; TODO: are there answers that should display differently?
          (eopl:pretty-print answer) (newline)
          (rep))))  ; tail-recursive, so stack doesn't grow.
    
    (define eval-one-exp
      (lambda (x) (top-level-eval (parse-exp x))))