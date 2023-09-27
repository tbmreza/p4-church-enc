#lang racket

(require rackunit racket/hash "definitions.rkt")
;; Assignment 4: A church-compiler for Scheme, to Lambda-calculus

(provide (all-defined-out))

; (provide church-compile
;          church->boolean
;          ; provided conversions:
;          church->nat
;          church->bool
;          church->listof)


;; Input language:
;
; e ::= (letrec ([x (lambda (x ...) e)]) e)    
;     | (let ([x e] ...) e)  
;     | (let* ([x e] ...) e)
;     | (lambda (x ...) e)
;     | (e e ...)    
;     | x  
;     | (and e ...) | (or e ...)
;     | (if e e e)
;     | (prim e) | (prim e e)
;     | datum
; datum ::= nat | (quote ()) | #t | #f 
; nat ::= 0 | 1 | 2 | ... 
; x is a symbol
; prim is a primitive operation in list prims
; The following are *extra credit*: -, =, sub1  
(define prims '(+ * - = add1 sub1 cons car cdr null? not zero?))

; ops module
(define (church->boolean tf)
  ((tf #t) #f))

; (define TRUE   (lambda (a) (lambda (_) a)))
; (define FALSE  (lambda (_) (lambda (b) b)))
; (define NOT    (λ (b) ((b FALSE) TRUE)))
; ; (check-true (church->boolean (NOT FALSE)))
; ; explains churchify if
; ; ((FALSE 2) 4)

(define ZERO? (λ (n) ((n (λ (_) FALSE)) TRUE)))
; (check-false (church->boolean (ZERO? (lambda (f) (lambda (x) (f x))))))
; (check-true (church->boolean (ZERO? (lambda (_) (lambda (x) x)))))

; This input language has semantics identical to Scheme / Racket, except:
;   + You will not be provided code that yields any kind of error in Racket
;   + You do not need to treat non-boolean values as #t at if, and, or forms
;   + primitive operations are either strictly unary (add1 sub1 null? zero? not car cdr), 
;                                           or binary (+ - * = cons)
;   + There will be no variadic functions or applications---but any fixed arity is allowed

;; Output language:

; e ::= (lambda (x) e)
;     | (e e)
;     | x
;
; also as interpreted by Racket


;; Using the following decoding functions:

; A church-encoded nat is a function taking an f, and x, returning (f^n x)
; Takes in evaled church-compile output. Expect (church->nat (eval (church-compile input) ...)) to be $answer.
(define (church->nat c-nat)
  ((c-nat add1) 0))

; A church-encoded bool is a function taking a true-thunk and false-thunk,
;   returning (true-thunk) when true, and (false-thunk) when false
(define (church->bool c-bool)
  ((c-bool (lambda (_) #t)) (lambda (_) #f)))
; (check-true ((church->bool TRUE) '()))

; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning when-cons applied on the car and cdr elements
; A church-encoded cons-cell is a function taking a when-cons callback, and a when-null callback (thunk),
;   returning the when-null thunk, applied on a dummy value (arbitrary value that will be thrown away)
(define ((church->listof T) c-lst)
  ; when it's a pair, convert the element with T, and the tail with (church->listof T)
  ((c-lst (lambda (a) (lambda (b) (cons (T a) ((church->listof T) b)))))
   ; when it's null, return Racket's null
   (lambda (_) '())))


;; Write your church-compiling code below:
; (require "definitions.rkt")

; (check-false (church->boolean (NULL? ((CONS NIL) NIL))))
; (check-eq? 100 (church->nat c100))
; (check-equal? (church->nat (cnat 3)) (church->nat (lambda (f) (lambda (x) (f (f (f x)))))))

(define (lookup bind-map op caller)
  (match (hash-ref bind-map op #f)
    [#f  (churchify op)]
    [v v]))

(define/contract (bind-map-new binds)
  (-> list? hash?)
  (define (f kv)
    (define e (second kv))
    (cons (first kv) (churchify e)))

  (make-immutable-hash (map f binds)))

(define/contract (bind-map-set outer binds)
  (-> hash? list? hash?)
  (define (f kv)
    (define e (second kv))
    ; pattern in cond branch?

    (define v (match e
      [`(lambda (,args ...) ,body)            (begin (displayln e)(lambda args body))]
      [_  (cond [(number? e)                  (cnat e)]
		[(not (hash-ref outer e #f))  (ll e outer)]
		[else                         (hash-ref outer e)])]))

    ; (define v (cond [(number? e)  (cnat e)]
	; 	    ; In racket, (not (hash-ref ... #f)) is true only if hash-ref returns #f.
	; 	    ; More naturally: if outer doesn't contain e, perform ll on it.
	; 	    [(not (hash-ref outer e #f))  (ll e outer)]  ; lambda e not found in here...
	; 	    [ else  (match e
	; 		      [`(lambda (,args ...) ,body)  e]
	; 		      [_                            (hash-ref outer e)])]))

    ; (define v (cond [(number? e)  (cnat e)]
	; 	    ; In racket, (not (hash-ref ... #f)) is true only if hash-ref returns #f.
	; 	    ; More naturally: if outer doesn't contain e, perform ll on it.
	; 	    [(not (hash-ref outer e #f))  (ll e outer)]
	; 	    [ else                        (hash-ref outer e)]))

    (if (procedure? v) (void) (raise-result-error (string->symbol "result type") "procedure?" v))

    (cons (first kv) v))
    
  (hash-union outer (make-immutable-hash (map f binds)) #:combine/key (lambda (_k _v1 v2) v2)))

(define/contract (bind-map-set* outer binds)
  (-> hash? list? hash?)
  (define (f* bind acc)
    (define e (second bind))
    (define v (cond [(number? e)                  (cnat e)]
		    [(member e (hash-keys acc))   (hash-ref acc e)]
		    [(not (hash-ref outer e #f))  (ll e outer)]
		    [ else                        (hash-ref outer e)]))
    (hash-set acc (first bind) v))

  (define bm (foldl f* (hash) binds))
  (hash-union outer bm #:combine/key (lambda (_k _v1 v2) v2)))

(define/contract (ll body bind-map)
  (-> any? any? procedure?)
  (begin (display "ll body: ")(displayln body)(define res (match body
    [`'()                 NIL]
    ['#t                  TRUE]
    ['#f                  FALSE]
    [(? number? body)     (cnat body)]
    [`(if ,b ,then ,els)  ((((ll b bind-map) (lambda () (ll then bind-map))) (lambda () (ll els bind-map))))]

    ; Rearrange binary? body so that eventually we can immediately invoke ((lambda (fn) (fn op arg)) body)
    [`(,(? binary? op) (,arg1 ...) (,arg2 ...))
      (ll `(,op ,(ll arg1 bind-map) ,(ll arg2 bind-map)) bind-map)]

    [`(,(? binary? op) (,arg1 ...) ,arg2)
      (ll `(,op ,(ll arg1 bind-map) ,arg2) bind-map)]

    [`(,(? binary? op) ,arg1 (,arg2 ...))
      (ll `(,op ,arg1 ,(ll arg2 bind-map)) bind-map)]

    [`(,(? binary? op) ,arg1 ,arg2)
      ((lambda (fn) (fn (lookup bind-map op "") (lookup bind-map arg1 "") (lookup bind-map arg2 "")))
       (lambda (op arg1 arg2) ((op arg1) arg2)))]

    [`(,(? unary? op) (,arg ...))
      (begin (ll `(,op ,(ll arg bind-map)) bind-map))]

    [`(,(? unary? op) ,arg)
      ; (ll `(,op ,(lookup bind-map arg "")))
      (begin
	((lambda (fn) (fn (lookup bind-map op "") (lookup bind-map arg "")))
	 (lambda (op arg) (op arg))))]

    [`(,lhs ,rhs)
      ; ((lambda (fn) (fn (lookup bind-map lhs "") (lookup bind-map arg "")))
	;  (lambda (op arg) (op arg)))
      (begin
	(match c0
	  [_  ((lambda (num) (num c3)) (ll rhs bind-map))]))]

    [`(lambda (,formal-params ...) ,body)
      (begin
	(define (lookup-free-vars body formal-params bind-map)
	  (define (f var)
	    (cond [(number? var)               (cnat var)]
		  [(member var formal-params)  var]
		  [else                        (lookup bind-map var "")]))
	  (define (mk)
	    (map f body))
	  (evalnew `(lambda ,formal-params ,(mk))))

	(lookup-free-vars body formal-params bind-map))]

    [`(let ,binds2 ,e)
      (begin
	(ll e (bind-map-set bind-map binds2)))]

    [`(let* ,binds2 ,e)                (ll e (bind-map-set* bind-map binds2))]
  ; [`(letrec ,binds2 ,e)              (?? e (?? binds2))]

    ; [_  '()]
    [v  v]
    )) res)

  )

(define/contract (churchify e)
  (-> any? procedure?)
  (match e
    [(? number? e)                   (cnat e)]
    [`'()                            NIL]
    ['#t                             TRUE]
    ['#f                             FALSE]
    [`(if ,b ,then ,els)             ((((churchify b) (lambda () (churchify then))) (lambda () (churchify els))))]
    [`(let ,binds ,e)                (ll e (bind-map-new binds))]
    [_ e]))

; (check-false (church->boolean (churchify `(let ([not ,NOT])(not #t)))))
; (check-false ((church->bool (churchify `(let ([not ,NOT])(not #t)))) '()))
; (check-eq? 2 (church->nat (churchify `(if #t 2 3)))) ;-> c2
; (check-true (church->boolean (churchify `(if #t #t #f))))

; (check-equal? (church->nat (SUCC (lambda (_) (lambda (x) x)))) (church->nat (lambda (f) (lambda (x) (f x)))))
; (check-equal? (church->nat ((PLUS c2) c3)) 5)
; (check-equal? (church->nat ((MUL c3) c3)) 9)
; (check-equal? (church->nat ((POW c3) c2)) 8)

; (define ccar         (λ (l) ((l (λ (a b) a))  (λ () #f))))
; (define cnil?        (λ (l) ((l (λ (a b) #f)) (λ () #t))))  ; from slide
; (define cnil         (λ (c) (λ (n) (n))))
; (cons a b) = (λ (when-cons) (λ (when-null) (when-cons a b)))
; (define (ccons a b) (λ (c) (λ (n) (c a b))))
; (define (ccons a b) (λ (n) (n a b)))

; (define PAIR (λ (a) (λ (b) (λ (s) ((s a) b)))))
; (define CAROLD  (λ (p) (p TRUE)))
; (define CDROLD  (λ (p) (p FALSE)))
; (define NIL FALSE)
; (define NIL? (λ (p) (??)))


; lists.rkt
; (check-eq? (church->nat (CAROLD ((PAIR c4) NIL))) 4)
; (check-eq? (church->nat (CAROLD ((PAIR c4) FALSE))) 4)
; (check-eq? (church->nat (CDR ((PAIR c4) c2))) 2)
; can this car operate on our CONS
; one requires NIL in the base, the other requires FALSE 

; ((CONS c2) ((CONS c3) NIL))
; (check-equal? ((church->listof church->nat) (CAR ((CONS ((CONS c2) ((CONS c3) NIL))) NIL))) '(2 3))

; (CDR ((PAIR c4) TRUE))
; ((CONZ c4) NIL)
; (check-eq? (church->nat (CAROLD ((CONZ c4) FALSE))) 4)

; One intuition (immediate observation of a simpler definition, not the one implemented below. The implementation below is called "wisdom tooth trick" for some intuition I can't work out yet.)
; of PRED is we start with a pair of zeros ((CONS c0) c0).
; 
; If we input c0 (a lambda that *ignores* its outer-most parameter f), we take the first of our pair.
; 
; If we input c1 (a lambda that applies f *once*), we take the second of previous step c0 as our new first; our new second succ of that new first;
;   and finally return the first of our pair.
; 
; We increase the number of swapping-incrementing dance steps as we increment our input. (PRED k+1) leads (PRED k) by one because we do the dance one more time,
; by definition of church numerals.
; (define CAROLD  (λ (p) (p TRUE)))
; (define T (λ (p) ((PAIR (SUCC (CAROLD p))) (CAROLD p))))
; (define PRED (λ (n) (CDROLD ((n T) ((PAIR c0) c0)))))
; (check-eq? (church->nat (PRED c4)) 3)

; (define MINUS (lambda (m) (lambda (n) ((n PRED) m))))
; (check-eq? (church->nat ((MINUS c4) c3)) 1)

; https://en.wikipedia.org/wiki/Church_encoding#Represent_the_list_using_right_fold
; 
; church pair defs:
(define cpair    (λ (a) (λ (b) (λ (n) (n (a b))))))
(define cfirst   (λ (p) (p (λ (x) (λ (y) x)))))
(define csecond  (λ (p) (p (λ (x) (λ (y) y)))))
; (check-eq? (church->nat (cfirst ((cpair c0) c3))) (church->nat (cfirst ((cpair c0) c2))))
; (check-eq? (church->nat (FALSE ((cpair c1) c2))) (church->nat (csecond ((cpair c0) c2))))
;
; right fold functions:
; (define (ccons a b) (λ (c) (λ (n) (c a b))))
; slide:
; ‘() = (λ (when-cons) (λ (when-null)
;  (when-null)))
;
; (cons a b) = (λ (when-cons) (λ (when-null) (when-cons a b)))


(define c30 ((MUL ((MUL c3) c2)) ((PLUS c3) c2)))
; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)

; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
; Build a let expression containing all helpers and the input program.
; Delegate the expression to churchify.
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (churchify
   `(let ([add1 ,SUCC]
          [sub1 ,PRED]
          [cons ,CONS]
          [null? ,NULL?]
          [not ,NOT]
          [car ,CAR]
          [cdr ,CDR]
          [zero? ,ZERO?]
          [+ ,PLUS]
          [- ,MINUS]
          [* ,MUL])
      ,program)))

; (check-true (church->boolean (churchify `(let ([not ,NOT]) (not #f)))))
; (check-eq? 6 (church->nat (churchify `(let ([* ,MUL]) (* 2 3)))))
; (check-eq? 4 (church->nat (churchify `(let () (if #t 4 3)))))
; (check-eq? 3 (church->nat (churchify `(let ([not ,NOT]) (if (not #f) 3 5)))))
; (check-eq? 3 (church->nat (churchify `(let ([ad ,SUCC]) (ad 2)))))
; (check-eq? 7 (church->nat (churchify `(let ([b 6][ad ,SUCC]) (ad b)))))
; (check-eq? 6 (church->nat (churchify `(let ([b 3][ad ,SUCC]) (ad (ad (ad b)))))))
; (check-eq? 12 (church->nat (churchify `(let ([b 3][* ,MUL]) (* b 4)))))
; (check-eq? 27 (church->nat (churchify `(let ([b 3][* ,MUL]) (* b (* b 3))))))

; ; enhance regular let with ability to store lambda: reg
; (define prog
;   '(let ([id (lambda (lst) lst)])
;      (id 14)))

; ; ... with lookup still working: reg
; (define prog
;   '(let ([id (lambda (lst) lst)][b 13])
;      (id b)))

; ; unused lambda param: ok
; (define prog
;   '(let ([id (lambda (_lst) 14)][b 13])
;      (id b)))

; ; inlined lambda
; (define prog
;   '(let ([ignore 13])
;      ((lambda (num) (num 3)) (lambda (x) (add1 x)))))

; lambda wrapped unary op
(define prog
  '(let ([ignore 13])
     (lambda (x) (add1 x))))
     ; (lambda (x) (sub1 x))))

(define compiled (church-compile prog))
(define cv-comp (eval compiled (make-base-namespace)))
(church->nat (cv-comp c3))

; (define compiled (church-compile prog))
; (define cv-comp (eval compiled (make-base-namespace)))
; (define unchurch church->nat)
; (define v-comp (unchurch cv-comp))
; (display 'v-comp)(displayln v-comp)
