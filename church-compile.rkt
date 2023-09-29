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

; logs:
; only ll default arm calls lookup
; churchify and ll shouldn't overlap in terminal arms
; nesting lambda means growing fargs
(define (lookup op bind-map)
  (cond [(procedure? op)  op]
        [else             (hash-ref bind-map op #f)]))

(define/contract (bind-map-new binds)
  (-> list? hash?)
  (define (f kv)
    (define e (second kv))
    (cons (first kv) (churchify e)))

  (make-immutable-hash (map f binds)))

(define/contract (bind-map-set binds outer)
  (-> list? hash? hash?)
  (define (f kv)
    (define e (second kv))
    (define v (cond [(number? e)                  (cnat e)]
                    [(not (hash-ref outer e #f))  (ll e outer)]
                    [else                         (hash-ref outer e)]))

    (if (procedure? v)
      (void)
      (raise-result-error (string->symbol "church-encoded type") "procedure?" v))

    (cons (first kv) v))
    
  (define bm (make-immutable-hash (map f binds)))
  (hash-union outer
              bm
              #:combine/key (lambda (_k _v1 v2) v2)))

(define/contract (bind-map-set* binds outer)
  (-> list? hash? hash?)
  (define (f* bind acc)
    (define e (second bind))
    (define v (cond [(number? e)                  (cnat e)]
                    [(member e (hash-keys acc))   (hash-ref acc e)]
                    [(not (hash-ref outer e #f))  (begin (ll e acc))]
                    [else                         (hash-ref outer e)]))
    (hash-set acc (first bind) v))

  (define bm (foldl f* outer binds))
  (hash-union outer
              bm
              #:combine/key (lambda (_k _v1 v2) v2)))

(define/contract (ll body bind-map)
  (-> any? any? procedure?)
  (match body
    [(? literal? body)  (churchify-terminal body)]

    [`(if ,b ,then ,els)
      (begin
        ((((ll b bind-map) (lambda () (ll then bind-map))) (lambda () (ll els bind-map)))))]

    [`(,(? binary? op) ,a1 ,a2)
      (begin
        (define (val e) (ll e bind-map))

        ((lambda (fn) (fn (val op) (val a1) (val a2)))
         (lambda (op a1 a2) ((op a1) a2))))]

    [`(,(? unary? op) ,arg)
      (begin
        (define (val e) (ll e bind-map))

        ((lambda (fn) (fn (val op) (val arg)))
         (lambda (op arg) (op arg))))]

    [`(,op ,arg)
      (begin
        ((ll op bind-map) (ll arg bind-map)))]

    [`(lambda (,fargs ...) ,body/n)
      (begin
        ; Fill body with current bind-map, leaving body only with its formal args.
        ; Implicit: use ll's bind-map.
        (define/contract (fill-free-vars e fargs)
          (-> any? any? any?)
          (begin
            (match e
              [`(lambda (,fargs/n ...) ,body/n/n)
                (begin
                  `(lambda ,fargs/n ,(fill-free-vars body/n/n (append fargs fargs/n))))]

              [`(if ,b ,then ,els)
                (begin
                  (display 'b)(displayln b)
                  (define (ffv e) (fill-free-vars e fargs))
                  (define res (ffv b))
                  (display 'res)(displayln res)
                  ; verif that ffv b works on vars that were defined in prev square brackets.
                  ; next case would be var value provided in lambda body.
                  `(if ,(ffv b) ,(ffv then) ,(ffv els)))]

              [`(,(? binary? op) ,a1 ,a2)
                (begin
                  (fill-free-vars `((,op ,a1) ,a2) fargs))]

              [`(,op ,arg)
                (begin
                  (define (ffv e) (fill-free-vars e fargs))
                  (define (h var)
                    (match var
                      [`(,op/n ,arg/n)  `(,(ffv op/n) ,(ffv arg/n))]
                      [var              (ffv var)]))

                  `(,(h op) ,(h arg)))]

              [var
                (begin
                  (cond [(member var fargs)  var]
                        [else                (ll var bind-map)]))])))

        (evalnew `(lambda ,fargs ,(fill-free-vars body/n fargs))))]

    [`(letrec ,binds/n ,e)
      (begin
        (define (adapt todo) todo)
        (ll `(let ,(adapt binds/n) ,e)))]

    [`(let ,binds/n ,e)
      (begin
        (define bm (bind-map-set binds/n bind-map))
        (ll e bm))]

    [`(let* ,binds/n ,e)
      (begin
        (define bm (bind-map-set* binds/n bind-map))
        (ll e bm))]

    [v  (lookup v bind-map)]))

(define/contract (churchify-terminal l)
  (-> literal? procedure?)
  (match l
    [(? number? l)  (cnat l)]
    ['#t            TRUE]
    ['#f            FALSE]
    [`'()           NIL]
    [_ 'unreachable]))

(define/contract (churchify e)
  (-> any? procedure?)
  (match e
    [(? literal? e)    (churchify-terminal e)]
    [`(let ,binds ,e)  (ll e (bind-map-new binds))]
    [proc proc]))

; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)

; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
; Build a let expression containing all helpers and the input program.
; Delegate the expression to churchify.
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (churchify
   `(let (
          [add1 ,SUCC]
          [succ ,SUCC]
          [null? ,NULL?]
          [nil? ,NULL?]
          [sub1 ,PRED]
          [cons ,CONS]
          [not ,NOT]
          [and ,AND]
          [car ,CAR]
          [cdr ,CDR]
          [= ,EQ?]
          [+ ,PLUS]

          [nol? ,ZERO?]
          [zero? ,ZERO?]
          [- ,MINUS]
          [* ,MUL]
    )
      ,program)))

; verif slide example
(define prog
  `(let ([f (,Y (lambda (f)
      (lambda (x)
        ; (if (= x 0) 1 (* x (f (- x 1)))))))]) (f 20)))
        ; (if (zero? x) 1 (* x (f (- x 1)))))))]) (f 20)))
        (if (,ZERO? x) 1 (* x (f (- x 1)))))))]) (f 20)))

; (define compiled (church-compile prog))
; (define cv-comp (eval compiled (make-base-namespace)))
; (define unchurch church->nat)
; (define v-comp (unchurch cv-comp))
; (displayln v-comp)
