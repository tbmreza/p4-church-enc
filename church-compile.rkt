#lang racket

(require racket/hash "definitions.rkt")
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
; Example usage: (check-true ((church->bool test) '()))
(define (church->bool c-bool)
  ((c-bool (lambda (_) #t)) (lambda (_) #f)))
(define (church->boolean b)
  ((church->bool b) '()))

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

; (define (matches-lambda? v) #t)

(define (lookup bind-map op)
  (match (hash-ref bind-map op #f)
    [#f #:when (or (boolean? op)(number? op)(procedure? op))
     (begin
       (churchify op))]
    [v
      (begin
	v)])
  )

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
    (define v (cond [(number? e)                  (cnat e)]
		    [(not (hash-ref outer e #f))  (ll e outer)]
		    [else                         (hash-ref outer e)]))

    (if (procedure? v) (void) (raise-result-error (string->symbol "result type") "procedure?" v))

    (cons (first kv) v))
    
  (define res (hash-union outer (make-immutable-hash (map f binds)) #:combine/key (lambda (_k _v1 v2) v2)))
  ; (display 'bmsret)(displayln res)
  res)

(define/contract (bind-map-set* outer binds)
  (-> hash? list? hash?)
  (define (f* bind acc)
    (define e (second bind))
    (define v (cond [(number? e)                  (cnat e)]
		    [(member e (hash-keys acc))   (hash-ref acc e)]
		    ; [(not (hash-ref outer e #f))  (begin (display 'BMS:)(displayln e)(ll e outer))]
		    [(not (hash-ref outer e #f))
		     (begin
		       ; (display 'BMS:)(displayln e)
		       (ll e acc))]
		    [ else                        (hash-ref outer e)]))
    (define vret (hash-set acc (first bind) v))
    ; (display 'vret)(displayln vret)
    vret)

  ; (define bm (foldl f* (hash) binds))
  (define bm (foldl f* outer binds))

  (hash-union outer bm #:combine/key (lambda (_k _v1 v2) v2)))

(define/contract (ll body bind-map)
  (-> any? any? procedure?)
  (begin
    (define res (match body
    [`'()                 NIL]
    ['#t                  TRUE]
    ['#f                  FALSE]
    [(? number? body)     (cnat body)]
    [`(if ,b ,then ,els)  (begin ((((ll b bind-map) (lambda () (ll then bind-map))) (lambda () (ll els bind-map)))))]

    ; Rearrange binary? body so that eventually we can immediately invoke ((lambda (fn) (fn op arg)) body)
    [`(,(? binary? op) (,arg1 ...) (,arg2 ...))
      (ll `(,op ,(ll arg1 bind-map) ,(ll arg2 bind-map)) bind-map)]

    [`(,(? binary? op) (,arg1 ...) ,arg2)
      (ll `(,op ,(ll arg1 bind-map) ,arg2) bind-map)]

    [`(,(? binary? op) ,arg1 (,arg2 ...))
      (ll `(,op ,arg1 ,(ll arg2 bind-map)) bind-map)]

    [`(,(? binary? op) ,arg1 ,arg2)
      (begin
	(define op-val (lookup bind-map op))
	(define arg1-val (lookup bind-map arg1))
	(define arg2-val (lookup bind-map arg2))

	((lambda (fn) (fn op-val arg1-val arg2-val))
	 (lambda (op arg1 arg2) ((op arg1) arg2))))]

    [`(,(? unary? op) (,arg ...))
      (begin (ll `(,op ,(ll arg bind-map)) bind-map))]

    [`(,(? unary? op) ,arg)
      (begin
	((lambda (fn) (fn (lookup bind-map op) (lookup bind-map arg)))
	 (lambda (op arg) (op arg))))]

    [`(,op ,arg)
      (begin
	(match op
	  [op  #:when (member op (list 'len 'f))
	       (begin
		 ; (displayln op)
		 ((lookup bind-map op) (ll arg bind-map)))]
	  [`(lambda (,_formal-params ...) ,_body)  ((ll op bind-map) (ll arg bind-map))]
        ; [(? matches-lambda? op)                  ((lookup bind-map op) (ll arg bind-map))]
        [_
	  (begin
	    (define lhs (ll op bind-map))
	    (define rhs (ll arg bind-map))
	    (define ret (lhs rhs)) ret)]
	; ((ll op bind-map) (ll arg bind-map)))]
	)
	)]

    [`(lambda (,formal-params ...) ,body)
      (begin
	(define/contract (fill-free-vars body)
	  (-> any? any?)
	  (begin
	    ; (display 'body)(displayln body)
	    (match body
	      [`(if ,b ,then ,els)
		(begin
		  (define fv-then (fill-free-vars then))
		  (define fv-els (fill-free-vars els))
		  ; filling b without reg `(if ,b ,(fill-free-vars then) ,(fill-free-vars els)))]
		  `(if ,b ,fv-then ,fv-els))]

	      [`(lambda (,formal-params2 ...) ,body2)
		(begin `(lambda ,formal-params2 ,(fill-free-vars body2)))]

	      ; applications (prims or not) have body of length 2.
	      [body #:when (len-is-2? body) 
		(begin
		  (define (f var)
		    (match var
		      [(? number? var)                               (cnat var)]
		      [var #:when (member var formal-params)         var]
		      [var #:when (member var (hash-keys bind-map))  (lookup bind-map var)]
		      [`(,a ,b)                                      `(,(f a) ,(f b))]
		      [v v]))
		  (map f body))]

	      [var
		(begin
		  (ll var bind-map)
		  )])))

	; ; ok
	; (define t1 (list '7 c7))
	; ; (check-true #f)
	; (check-eq? (church->nat (fill-free-vars (first t1))) (church->nat (second t1)))
	

	(evalnew `(lambda ,formal-params ,(fill-free-vars body))))]




    [`(letrec ,binds2 ,e)
	(begin
	  (define/contract (polyfill name fn-value)
          ; (-> symbol? matches-lambda? any?)
	    (-> symbol? any? any?)
	    `(,name (,Y (lambda (,name) ,fn-value))))

	  (define f1 (first binds2))
	  (define res (polyfill 'len (second f1)))
	  (displayln res)
	  (define pf (second res))

	  (define (f bind)
	    (match bind
	      [`(,name (lambda (,formal-params ...) ,body))  (polyfill name (second bind))]
	      [kv kv]))

	  (define polyfilled-binds2 (map f binds2))
	  ; (define bms (bind-map-set bind-map polyfilled-binds2))
	  ; (ll e (bind-map-set bind-map polyfilled-binds2))
	  c0
	  )]

    [`(let ,binds2 ,e)
      (begin
	(ll e (bind-map-set bind-map binds2)))]

    [`(let* ,binds2 ,e)
      (begin
	(define bms (bind-map-set* bind-map binds2))
	(define ret (ll e bms))
	ret)]

    [v  (begin
	  v)]
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
    [_
      (begin
	e)]))

; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)

; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
; Build a let expression containing all helpers and the input program.
; Delegate the expression to churchify.
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (churchify
   `(let ([add1 ,SUCC]
	  [succ ,SUCC]
	  [null? ,NULL?]
          [sub1 ,PRED]
          [cons ,CONS]
          [not ,NOT]
          [and ,AND]
          [car ,CAR]
          [cdr ,CDR]
          [nol? ,ZERO?]
          [zero? ,ZERO?]
          [= ,EQ?]
          [+ ,PLUS]
          [- ,MINUS]
          [* ,MUL]
	  )
      ,program)))

; ; goal
; (define prog
;   '(letrec ([len (lambda (lst)
;                    (if (null? lst)
;                        0
;                        (add1 (len (cdr lst)))))])
;      (len (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 (cons '() '())))))))))

; verif slide example
(define prog
  `(let ([f (,Y (lambda (f)
		  (lambda (x)
		    ; (if (= x 0) 1 (* x (f (- x 1)))))))]) (f 20)))
		    ; (if (zero? x) 1 (* x (f (- x 1)))))))]) (f 20)))
		    (if (,ZERO? x) 1 (* x (f (- x 1)))))))]) (f 20)))

; ; let body can be a curried lambda: yes, but not applying the args in the body yet
; ; (((lambda (a) (lambda (b) (+ a b))) 12) 13)
; ; (churchify `(let ([+ ,PLUS])
; ; 	      (((lambda (a) (lambda (b) (+ a b))) 12) 13)))
; ; (churchify `(let ([add1 ,SUCC])
; ; 	      (((lambda (a) (lambda (b) (a b))) add1) 6)))
; (define cc (churchify `(let ([add1 ,SUCC])
; 	      (lambda (a) (lambda (b) (a b))))))
; (church->nat ((cc PRED) c4))

; (define compiled (church-compile prog))
; (define cv-comp (eval compiled (make-base-namespace)))
; (define unchurch church->nat)
; (define v-comp (unchurch cv-comp))
; (displayln v-comp)
