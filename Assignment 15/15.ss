;Joshua Palamuttam
;Assignment 15

;Problem 1
(define apply-continuation
    (lambda (k v) (k v)))
;a
(define member?-cps
    (lambda (sym ls k)
    (cond[(null? ls) (apply-continuation k #f)]
    [(eq? sym (car ls))(apply-continuation k #t)]
    [else (member?-cps sym (cdr ls) k)])))
;b
(define (set?-cps ls k)
 (cond [(null? ls) (apply-continuation k #t)]
 [(not(pair? ls)) (apply-continuation k #f)]
 [else (set?-cps (cdr ls) 
   (lambda (cdr-set)
    (member?-cps (car ls) (cdr ls)
        (lambda (cdr-in-set)
            (if cdr-in-set
              (apply-continuation k #f)
              (apply-continuation k cdr-set))))))]))
;c
(define (set-of-cps ls k )
 (set-of-cps-helper-cps ls '() k))

(define (set-of-cps-helper-cps ls result k)
 (cond [(null? ls) (apply-continuation k result)]
 [else (member?-cps (car ls) (cdr ls) 
 (lambda (x)
  (if x
     (set-of-cps-helper-cps (cdr ls) result k)
     (set-of-cps-helper-cps (cdr ls) (append result (list(car ls))) k))))]))
(define (1st-cps ls k)
 (apply-continuation k (car ls))
)

(define (map-cps proc ls k)
(cond [(null? ls) (apply-continuation k '())]
    [else (map-cps proc (cdr ls) 
    (lambda (mapped-cdr)
     (proc (car ls)
     (lambda (mapped-car)
      (apply-continuation k (cons mapped-car mapped-cdr))))))]))

(define (domain-cps los k)
      (map-cps 1st-cps los 
        (lambda (mapped-val)
         (set-of-cps mapped-val 
            (lambda (set-val)
             (apply-continuation k set-val))))))

;d
(define (make-cps prim-proc)
 (lambda (x k)
  (apply-continuation k (prim-proc x))))
;e
(define (andmap-cps pred-cps ls k)
 (cond [(null? ls) (apply-continuation k #t)]
    [else (pred-cps (car ls) 
     (lambda (carred-pred)
      (if carred-pred
       (andmap-cps pred-cps (cdr ls) 
        (lambda (andmapped-cdr)
         (apply-continuation k andmapped-cdr)
        ))
       (apply-continuation k #f))))]))

;f
; (define snlist-recur
;     (lambda (seed item-proc list-proc)
;     (letrec ([helper-cps
;     (lambda (ls)
;     (if (null? ls)
;     seed
;    (let ([c (car ls)])
;     (if (or (pair? c) (null? c))
;     (list-proc (helper-cps c) (helper-cps (cdr ls)))
;     (item-proc c (helper-cps (cdr ls)))))))])
;     helper-cps)))

(define (cps-snlist-recur base item-proc-cps list-proc-cps)
(letrec ([helper (lambda (ls k)
    (if (null? ls)
        (apply-continuation k base)
        (let ([c (car ls)])
            (if (or (pair? c) (null? c))
                (helper c
                    (lambda (v)
                        (helper (cdr ls)
                            (lambda (x) (list-proc-cps v x k)))))
                (helper (cdr ls)
                    (lambda (v)
                        (item-proc-cps c v k)))))))])
helper)
)
(define (max-cps x y k)
(apply-continuation k (max x y))
)

(define (+-cps x y k)
(apply-continuation k (+ x y))
)

(define sn-list-depth-cps
(cps-snlist-recur 1
    (lambda (x y k)
        (apply-continuation k y))
    (lambda (x y k)
        (max-cps (+ x 1) y k)))
)

(define (append-cps ls1 ls2 k) ;Not CPS just realized this
(cond
    [(null? ls2) (apply-continuation k ls1)]
    [else (append-cps 
        (reverse (cons (car ls2) (reverse ls1))) (cdr ls2) k)]  
)
)

(define sn-list-reverse-cps
(cps-snlist-recur '()
    (lambda (x y k)
        (append-cps y (cons x '()) k))
    (lambda (x y k)
        (append-cps y (list x) k)))
)

(define (sn-list-occur-cps s slist k) ;Not CPS 
((cps-snlist-recur 0
    (lambda (x y k)
        (if (equal? s x)
            (+-cps 1 y k)
            (apply-continuation k y)))
    +-cps) slist k)
)

;The fib-memo function that we talked about in class uses a list to store all of the fibonacci numbers so the lookup time is O(n)
;The function that I wrote below for the new fibonacci memoized function uses a hashtable which is instant lookup a.k.a O(1).

;Problem 2
(define (memoize f hash eqp)
(let ([table (make-hashtable hash eqp)])
    (lambda args
        (let ([check (hashtable-ref table args #f)])
            (if check check
                (let ([result (apply f args)])
                    (hashtable-set! table args result)
                    result
                ))
        )    
    )
)
)

;Problem 3 worked with Manoj Kurapati on this problem
(define subst-leftmost
	(lambda (n o s p)
		(car (call-with-values (lambda () (let subst ([new n] [old o] [slist s] [pred p])
			(if (null? slist)
				(values '() #f)
				(if (pair? (car slist))					
						(let ([x (call-with-values (lambda () (subst new old (car slist) pred)) (lambda (slist found) (list slist found)))])
							(if (equal? (cadr x) #t)
								(values (cons (car x) (cdr slist)) #t)
								(let ([y (call-with-values (lambda () (subst new old (cdr slist) pred)) (lambda (slist found) (list slist found)))])
									(values (cons x (car y)) (cadr y)))))
					(if (null? (car slist))
						(let ([x (call-with-values (lambda () (subst new old (cdr slist) pred)) (lambda (slist found) (list slist found)))])
							(display (cons (car slist) x))
							(values (cons (car slist) (car x)) (cadr x)))

						(if (pred (car slist) old)
							(values (cons new (cdr slist)) #t)
							(let ([x (call-with-values (lambda () (subst new old (cdr slist) pred)) (lambda (slist found) (list slist found)))])

								(values (cons (car slist) (car x)) (cadr x)))))))))
		(lambda (slist found) (list slist found))))
		))