;; Ryan Bailey & Josh Palamuttam
;; Assignment 16

;: Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "C:/Users/baileyrj/Documents/Rose-Hulman/CS/PLC 304/Scheme/chez-init.ss")

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

    [lambda-improper-exp
     (id improper-list?)
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
     (id symbol?)
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
     (proc-names (list-of symbol?))
     (idss list?)
     (bodiess (list-of (list-of expression?)))
     (letrec-bodies (list-of expression?))]

    [named-let-exp
     (proc-id symbol?)
     (syms (list-of symbol?))
     (vals (list-of expression?))
     (body (list-of expression?))]
    
    [cond-exp
        (condition (list-of expression?))
        (body (list-of expression?))]
    
    [begin-exp 
        (bodies (list-of expression?))]

    [and-exp
        (first-pred expression?)
        (second-pred expression?)]

    [or-exp
        (body (list-of expression?))]

    [case-exp   
        (value expression?)
        (match list?) 
        (body list?)]

    [while-exp
        (condition expression?)
        (bodies (list-of expression?))]

    [define-exp
        (id symbol?)
        (body expression?)]

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
    (env list?)]
  [variable-args-closure
    (id symbol?)
    (bodies (list-of expression?))
    (env list?)]
  [improper-args-closure
    (id improper-list?)
    (bodies (list-of expression?))
    (env list?)])


(define-datatype reference reference?
    [ref
    (vec vector?)
    (index number?)])  
        
; (define-datatype form form?
;     [exp
;         (code expression?)]
;     [def
;         (definition definition?)])
     
; (define-datatype definition definition?
;     [variable-def
;         (id symbol?)
;         (body expression?)])
    

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

(define special-all-syms
    (lambda (improper)
        (if (or (null? (cdr improper)) (symbol? (cdr improper)))
            #t
            (and (symbol? (car improper)) (special-all-syms (cdr improper))))))

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
                    (if (not (proper-list? (2nd datum))) 
                        (if (special-all-syms (2nd datum))
                            (lambda-improper-exp (2nd datum) (map (lambda (y) (syntax-expand (parse-exp y))) (cddr datum)))
                            (eopl:error 'parse-exp "Error in parse-exp: lambda argument list: formals must be symbols: ~s" (2nd datum)))
                        (if (andmap (lambda (x) (symbol? x)) (2nd datum))
                            (lambda-exp (2nd datum) (map (lambda (y) (syntax-expand (parse-exp y))) (cddr datum)))
                            (eopl:error 'parse-exp "Error in parse-exp: lambda argument list: formals must be symbols: ~s" (2nd datum)))))    
              (if (< (length datum) 3)
                  (eopl:error 'parse-exp "Error in parse-exp: lambda expression: lambda expression missing body")
                  (lambda-no-paren-exp (2nd datum) (map (lambda (y) (syntax-expand (parse-exp y))) (cddr datum)))))]

       [(eqv? (1st datum) 'if)
          (if (or (< (length datum) 3) (> (length datum) 4))
              (eopl:error 'parse-exp "Error in parse-exp: if expression: should have (only test, then , and else clauses)")      
              (if (null? (cdddr datum))
                  (if-no-else-exp (syntax-expand (parse-exp (2nd datum)))
                                  (syntax-expand (parse-exp (3rd datum))))
                  (if-exp (syntax-expand (parse-exp (2nd datum)))
                      (syntax-expand (parse-exp (3rd datum)))
                      (syntax-expand (parse-exp (4th datum))))))]
      
       [(eqv? (1st datum) 'set!)
          (if (< (length datum) 3)
              (eopl:error 'parse-exp "Error in parse-exp: set!: missing expression: ~s" datum)
              (if (> (length datum) 3)
                  (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)
                  (set!-exp (2nd datum) (syntax-expand (parse-exp (3rd datum))))))]

        [(eqv? (1st datum) 'set-car!)
            (if (< (length datum) 3)
                (eopl:error 'parse-exp "Error in parse-exp: set!: missing expression: ~s" datum)
                (if (> (length datum) 3)
                    (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)
                    (set-car!-exp (2nd datum) (syntax-expand (parse-exp (3rd datum))))))]

        [(eqv? (1st datum) 'set-cdr!)
            (if (< (length datum) 3)
                (eopl:error 'parse-exp "Error in parse-exp: set!: missing expression: ~s" datum)
                (if (> (length datum) 3)
                    (eopl:error 'parse-exp "Error in parse-exp: set!: Too many parts: ~s" datum)
                    (set-cdr!-exp (2nd datum) (syntax-expand(parse-exp (3rd datum))))))]

       [(eqv? (1st datum) 'let)
              (if (< (length datum) 3)
                  (eopl:error 'parse-exp "Error in parse-exp: let expression: incorrect length: ~s" datum)
                  (if (and (not (pair? (2nd datum))) (not (null? (2nd datum)))) 
                    (named-let-exp (2nd datum) (map (lambda (x) (car x)) (3rd datum))  (map (lambda (x) (syntax-expand (parse-exp (cadr x)))) (3rd datum)) (map (lambda (y) (syntax-expand (parse-exp y))) (cdddr datum)))
                    (if (not (proper-list? (2nd datum)))
                          (eopl:error 'parse-exp "Error in parse-exp decls: not a proper list: ~s" (2nd datum))
                          (if (not (andmap proper-list? (2nd datum)))
                              (eopl:error 'parse-exp "Error in parse-exp: decls: not all proper lists: ~s" (2nd datum))
                              (if (not (andmap (lambda (x) (equal? (length x) 2)) (2nd datum)))
                                  (eopl:error 'parse-exp "Error in parse-exp: decls: not all length 2: ~s" (2nd datum))
                                  (if (not (andmap (lambda (x) (symbol? (car x))) (2nd datum)))
                                      (eopl:error 'parse-exp "Error in parse-exp: decls: first members must be symbols: ~s" (2nd datum))
                                      (if (or (pair? (2nd datum)) (null? (2nd datum)))
                                          (let-exp (map car (2nd datum)) (map (lambda (x) (syntax-expand (parse-exp (cadr x)))) (2nd datum)) (map (lambda (y) (syntax-expand (parse-exp y))) (cddr datum))) 
                                          (named-let-exp (2nd datum) (map (lambda (x) (car x)) (3rd datum))  (map (lambda (x) (syntax-expand (parse-exp (cadr x)))) (3rd datum)) (map (lambda (y) (syntax-expand (parse-exp y))) (cdddr datum))))))))))]

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
                                  (let*-exp (map car (2nd datum)) (map (lambda (x) (syntax-expand (parse-exp (cadr x)))) (2nd datum)) (map (lambda (y) (syntax-expand (parse-exp y))) (cddr datum)))))))))]

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
                                  (letrec-exp (map car (2nd datum)) 
                                              (map cadr (map cadr (2nd datum))) 
                                              (map (lambda (x) (list (syntax-expand (parse-exp x)))) (map car (map cddadr (2nd datum))))
                                              (list (syntax-expand (parse-exp (caddr datum)))))))))))]   
      [(eqv? (1st datum) 'cond)
        (cond-exp (map (lambda (x) (syntax-expand (parse-exp (car x)))) (cdr datum)) (map (lambda (x) (syntax-expand (parse-exp (cadr x)))) (cdr datum)))]
      [(eqv? (1st datum) 'case)
        (case-exp (syntax-expand (parse-exp (2nd datum))) (map car (cddr datum)) 
                                          (map (lambda (x) (syntax-expand (parse-exp (cadr x)))) (cddr datum)))]
      [(eqv? (1st datum) 'or)
        (or-exp (map (lambda (y) (syntax-expand (parse-exp y))) (cdr datum)))]
      [(eqv? (1st datum) 'and)
        (and-exp (syntax-expand (parse-exp (2nd datum))) (syntax-expand (parse-exp (3rd datum))))]  
      [(eqv? (1st datum) 'begin)
            (begin-exp (map (lambda (y) (syntax-expand (parse-exp y))) (cdr datum)))] 
      [(eqv? (1st datum) 'while)
        (while-exp (syntax-expand (parse-exp (2nd datum))) (map (lambda (y) (syntax-expand (parse-exp y))) (cddr datum)))]
      [(eqv? (1st datum) 'define)
            (define-exp (2nd datum) (syntax-expand (parse-exp (3rd datum))))] ;; Do we want to parse define? Should it be an expression?
       [else (if (or (not (proper-list? datum)) (not (proper-list? (cdr datum))))
                (eopl:error 'parse-exp "Error in parse-exp: application ~s is not a proper list" datum)
                (app-exp (syntax-expand (parse-exp (1st datum))) (map (lambda (y) (syntax-expand (parse-exp y))) (cdr datum))))])]
     [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define proper-list?
    (lambda (ls)
        (cond
            [(null? ls) #t]
            [else (and (or (null? (cdr ls)) (pair? (cdr ls))) (proper-list? (cdr ls)))])))
  
(define improper-list?
    (lambda (ls) (not (proper-list? ls))))

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
            [lambda-improper-exp (id body)
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
            ; [letrec-exp (syms vals body)
            ;     (append '(letrec) (join syms (map unparse-exp vals)) (map unparse-exp body))]
            [named-let-exp (proc-id syms vals body)
                (append '(let proc-id) (join syms (map unparse-exp vals)) (map unparse-exp body))]
            [case-exp (value match body) 1]
            [cond-exp (condition body) 1]
            [and-exp (first-pred second-pred) 1]
            [or-exp (body) 1]
            [begin-exp (bodies) 1]
            [while-exp (condition bodies) 1]
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
    (cons (cons syms vals)
           env)))

(define rib-find-position 
    (lambda (sym syms)
        (if (member sym syms)
                (cond 
                    [(eq? sym (car syms)) 0]
                    [else (+ 1 (rib-find-position sym (cdr syms)))])
            #f)))

(define apply-env 
    (lambda (env sym succeed fail)
        (if (null? env)
            (apply-env global-env sym succeed fail)                                  ;; Fail, the sym was not found
            (begin
                (let ([syms (caar env)]
                  [vals (cdar env)]
                  [less-env (cdr env)])
              (let ([pos (rib-find-position sym syms)])
                (if (number? pos)
                  (succeed (vector-ref vals pos))                   ;; Succeed, we found the sym
                  (apply-env less-env sym succeed fail))))))))


(define extend-env-recursively
    (lambda (proc-names idss bodiess old-env)
        (let ([len (length proc-names)])
            (let ([vec (make-vector len)])
                (let ([env (extend-env proc-names vec old-env)])
                    (for-each
                        (lambda (pos ids bodies)
                            (if (improper-list? ids)
                                (vector-set! vec
                                    pos
                                    (improper-args-closure ids bodies env)) 
                            (vector-set! vec
                                        pos
                                        (closure ids bodies env))))
                        (iota len)
                        idss
                        bodiess)
                    env)))))


(define (iota n)
    (let help-me ([n n] [count 0])
        (if (eq? n count) '()
            (cons count (help-me n (add1 count))))))
            


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

(define (syntax-expand exp)
    (cases expression exp
        [var-exp (id) exp]
        [lambda-exp (id body) exp]
        [lambda-no-paren-exp (id body) exp]
        [lambda-improper-exp (id body) exp]
        [lit-exp (id) exp]
        [if-exp (predicate true-case false-case) exp]
        [if-no-else-exp (predicate lone-case) exp]
        [set!-exp (id value) exp]
        [set-car!-exp (id value) exp]
        [set-cdr!-exp (id value) exp]
        [let-exp (syms vals body) (let->lambda syms vals body)]
        [let*-exp (syms vals body) 
            (let*->let syms vals body)]
        ; [letrec-exp (proc-names idss bodiess letrec-bodies)
        ;     (letrec->let proc-names idss bodiess letrec-bodies)]
        [letrec-exp (proc-names idss bodiess letrec-bodies) exp]
        [named-let-exp (proc-id syms vals body) (letrec-exp (list proc-id) (list syms) (list body) (list (app-exp (parse-exp proc-id) vals)))]
        [case-exp (value match body) 
            (make-case-ifs value match body)]
        [cond-exp (condition body)
            (if (equal? (car condition) '(var-exp else))
                (list 'if-no-else-exp (parse-exp #t) (car body))
                (list 'if-exp (car condition) (car body) (construct-ifs (cdr condition)  (cdr body))))]
        [and-exp (first-pred second-pred) 
            (list 'if-exp first-pred (construct-ifs (list second-pred '(var-exp else)) (list (parse-exp #t) (parse-exp #f))) (parse-exp #f))]
        [or-exp (body) 
            (if (null? body)
                (list 'if-no-else-exp (parse-exp #t) (parse-exp #f))
                (make-or-ifs body))]
        [begin-exp (bodies) (app-exp (lambda-exp '() (map syntax-expand bodies)) '())]
        [while-exp (condition bodies) exp]
        [app-exp (rator rand) exp]
        [define-exp (id body) exp]
        [else 1]))

(define (letrec->let proc-names idss bodiess letrec-bodies)
        (let-exp proc-names (make-nonsense proc-names) (append (make-set!s proc-names idss bodiess) letrec-bodies)))

(define make-set!s
    (lambda (proc-names idss bodiess)
        (cond 
            [(null? proc-names) '()]
            [(cons (set!-exp (car proc-names) (lambda-exp (car idss) (car bodiess))) 
                    (make-set!s (cdr proc-names) (cdr idss) (cdr bodiess)))])))

(define make-nonsense
    (lambda (proc-names)
        (cond 
            [(null? proc-names) '()]
            [(cons '(lit-exp 1) (make-nonsense (cdr proc-names)))])))




(define (let*->let syms vals bodies)
    (if (null? (cdr syms))
        (let-exp (list (car syms))  (list (car vals)) bodies)
        (let-exp (list (car syms)) (list (car vals)) (list (let*->let (cdr syms) (cdr vals) bodies)))))

; (define (expand-while-exp cond bodies)
;     (syntax-expand (letrec-exp '(loop) (list (lambda-exp '() (list (if-no-else-exp cond (begin-exp (append bodies (list (var-exp 'loop)))))))) (list (var-exp 'loop)))))

(define (let->lambda syms vals body)
    (app-exp (lambda-exp syms body) vals))


(define (make-case-ifs value match bodies)
    (if (equal? (car match) 'else)
        (car bodies)
        (if (null? (cdr bodies))
            (list 'if-no-else-exp (append '(app-exp (var-exp member)) (list (list value (cons 'lit-exp (list (car match)))))) (car bodies))
            (list 'if-exp (append '(app-exp (var-exp member)) (list (list value (cons 'lit-exp (list (car match)))))) (car bodies) (make-case-ifs value (cdr match) (cdr bodies))))))

(define (make-or-ifs bodies)
    (let ([bod (syntax-expand (car bodies))])
    (if (null? (cdr bodies))
        bod
        (let-exp '(or-var) (list bod) (list (if-exp (var-exp 'or-var) (var-exp 'or-var) (make-or-ifs (cdr bodies))))))))


(define (construct-ifs conds bodies)
    (if (equal? (car conds) '(var-exp else))
        (car bodies)
        (if (null? (cdr conds))
            (list 'if-no-else-exp (car conds) (car bodies))
            (list 'if-exp (car conds) (car bodies) (construct-ifs (cdr conds) (cdr bodies))))))



;-------------------+
;                   |
;   INTERPRETER     |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval 
  (lambda (parsed-form)
  (eval-exp parsed-form (empty-env))))
    ; (cases form parsed-form
    ;     [exp (code) (eval-exp parsed-form global-env)]
    ;     [def (definition) 1] ;; add what ever we are defining to the global environment
    ;     [else (eopl:error 'top-level-eval "Not a valid form - exp or def")])))  ;; Errrororoororor
    ; later we may add things that are not expressions.
    


(define identity-proc
    (lambda (x) x)) 
        
(define common-fail
    (lambda ()
        (eopl:error 'common_error "Error")))

; eval-exp is the main component of the interpreter

(define eval-exp  
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) datum]
      [var-exp (id)
        (apply-env env id                       ; look up its value.
            identity-proc                       ; identity procedure if it is in the environment 
                (lambda ()                      ; Fail case now applies the global environment
                    (apply-env init-global-env id 
                        identity-proc               ; Same identity on success
                        (lambda ()                  ; procedure to call if it is not in env
                            (eopl:error 'apply-env 
                                "variable not found in environment: ~s"
                                id)))))] 
      [lambda-exp (id body)
        (closure id body env)]
      [lambda-no-paren-exp (id body) 
        (variable-args-closure id body env)]
      [lambda-improper-exp (id body)
        (improper-args-closure id body env)]
      [let-exp (syms vals body)
        (let ([extended-env
                (extend-env syms
                            (list->vector (map (lambda (x) (eval-exp x env)) vals))
                            env)])
                (eval-bodies body extended-env))]
      [let*-exp (syms vals body) 1]
      [letrec-exp (proc-names idss bodiess letrec-bodies)
        (eval-bodies letrec-bodies
        (extend-env-recursively
            proc-names idss bodiess env))]
      [named-let-exp (proc-id syms vals body) 1]
      [if-exp (predicate true-case false-case) 
        (if (eval-exp predicate env)
            (eval-exp true-case env)
            (eval-exp false-case env))]
      [if-no-else-exp (predicate lone-case) (if (eval-exp predicate env)
                                                (eval-exp lone-case env))]
      [set!-exp (id value) 
            (set-ref! 
                (apply-env-ref env id)
                (eval-exp value env))]
      [set-car!-exp (id value)
            (apply-prim-proc 'set-car! (list (apply-env env id identity-proc common-fail) (apply (lambda (x) (eval-exp x env)) (list value))))]
      [set-cdr!-exp (id value)
            (apply-prim-proc 'set-cdr! (list (apply-env env id identity-proc common-fail) (apply (lambda (x) (eval-exp x env)) (list value))))]
      [while-exp (condition bodies) (eval-while-exp condition bodies env)]
      [define-exp (id body) (set! global-env (extend-env (list id) (list->vector (list (eval-exp body env))) global-env))
                            global-env]
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
    [else (error 'eval-exp "Bad abstract syntax: ~a" exp)])))

; evaluate the list of operands, putting results into a list

(define apply-env-ref 
    (lambda (env sym)
        (if (null? env)
            (apply-env-ref global-env sym)                                ;; Fail, the sym was not found
        (begin
            (let ([syms (caar env)]
              [vals (cdar env)]
              [env (cdr env)])
          (let ([pos (rib-find-position sym syms)])
            (if (number? pos)
              (ref vals pos)                   ;; Succeed, we found the sym
              (apply-env-ref env sym))))))))

(define deref 
    (lambda (x)
        (cases reference x
            [ref (vec index)
                (vector-ref vec index)])))

(define set-ref!
    (lambda (x value)
        (cases reference x
            [ref (vec index)
                (vector-set! vec index value)])))

(define (eval-while-exp cond bodies env)
    (letrec ([loop (lambda (cond bodies env)
        (if (eval-exp cond env)
            (begin 
                (eval-bodies bodies env)
                (loop cond bodies env))))]) 
    (loop cond bodies env)))

(define eval-rands
  (lambda (rands env)
    (map (lambda (e) (eval-exp e env)) rands)))

(define eval-bodies
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
        (let ([extended-env (extend-env ids (list->vector args) env)])
            (eval-bodies bodies extended-env))]
      [variable-args-closure (id bodies env)
        (let ([extended-env (extend-env (list id) (list->vector (list args)) env)])
            (eval-bodies bodies extended-env))]
      [improper-args-closure (id bodies env)
        (let ([extended-env (extend-env (improper->proper id) (list->vector (group-args id args)) env)])
            (eval-bodies bodies extended-env))]
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))

(define group-args 
    (lambda (improper-syms variable-args)
        (if (symbol? (cdr improper-syms))
            (cons (car variable-args) (list (cdr variable-args)))
            (cons (car variable-args) (group-args (cdr improper-syms) (cdr variable-args))))))

(define improper->proper
    (lambda (ls)
        (cond [(symbol? ls) (list ls)]
              [(null? (cdr ls)) '()]
              [else (cons (car ls) (improper->proper (cdr ls)))])))
                

(define *prim-proc-names* '(+ - * / add1 sub1 cons = list car cdr caar cddr cadr cdar cadar
                            not zero? >= > < <= null? equal? eq? pair? number? symbol? append 
                            list->vector list? vector->list vector? procedure? length set-car! set-cdr!
                            map apply vector vector-set! vector-ref member quotient list-tail eqv? assq))


(define init-global-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (list->vector (map prim-proc      
          *prim-proc-names*))
     (empty-env)))

(define reset-global-env
    (lambda () (set! global-env (make-init-env))))

(define make-init-env
    (lambda () init-global-env))

(define global-env init-global-env)

; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc  
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(/) (apply / args)]
      [(quotient) (quotient (1st args) (2nd args))] ;; probably need to apply here
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(assq) (assq (1st args) (2nd args))]
      [(append) (append (1st args) (2nd args))]
      [(map) (map (lambda (x) (apply-proc (1st args) (list x))) (2nd args))]
      [(apply) (apply-proc (1st args) (2nd args))]
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
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))]
      [(vector) (list->vector args)]
      [(vector?) (vector? (1st args))]
      [(list-tail) (list-tail (1st args) (2nd args))]
      [(null?) (null? (1st args))]
      [(pair?) (pair? (1st args))]
      [(number?) (number? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(procedure?) (proc-val? (1st args))]
      [(not) (not (1st args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(eqv?) (eqv? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(zero?) (zero? (1st args))]
      [(list?) (list? (1st args))]
      [(length) (length (1st args))]
      [(member) (member (1st args) (2nd args))]
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
    (let ([answer (top-level-eval (syntax-expand (parse-exp (read))))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)))))