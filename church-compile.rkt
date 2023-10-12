#lang racket

(require "definitions.rkt")
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

(define (churchify-terminal l)
  (match l
    [(? number? l)  (cnat l)]
    ['#t            TRUE]
    ['#f            FALSE]
    [`'()           NIL]))

; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)
(define (churchify e)
  (define (left-left bind acc)
    (match bind
      ['()           acc]
      [`(,x . (,e))
        `((lambda (,x) ,acc)  ,(churchify e))]))

  (match e
    [`(let* ,binds ,e-b)
      (foldr left-left (churchify e-b) binds)]

    [`(let ,binds ,e-b)
      (foldl left-left (churchify e-b) binds)]

    [(? literal? e)    (churchify-terminal e)]

    [`(if ,e0 ,e1 ,e2)
      `(,(churchify `(,(churchify e0) (lambda () ,(churchify e1)) (lambda () ,(churchify e2)))))]

    [`(lambda ,xs ,e-body)
      (define (h xs)
        (match xs
          ['()           (churchify e-body)]
          [`(,x . ,rst)  `(lambda (,x) ,(h rst))]))
      (h xs)]

    [`(,binary-op ,e1 ,e2)
      (display "inp:\t")(displayln e)
      (define bp
        `((,binary-op ,e1) ,e2)
      )
      (display "out:\t")(displayln bp)
      bp]

    [`(,op ,arg)
      (display "oa inp:\t")(displayln e)
      `(,(churchify op) ,(churchify arg))]

    [(not (? list? _))  e]

    [(? list es)
      (define (surround es)
        (match es
          [`(,fst ,snd . ,rst)  (surround `((,(churchify fst) ,(churchify snd)) ,@rst))]
          [es                   (first es)])) ; simple guy, I see pair of extraneous parens, I apply first. probably empty lists etc etc
      (surround es)]))

; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
; Build a let expression containing all helpers and the input program.
(define (church-compile program)
  (evalnew (churchify
    `(let ([add1 ,SUCC] [null? ,NULL?] [sub1 ,PRED] [cons ,CONS] [not ,NOT] [and ,AND] [car ,CAR]
           [cdr ,CDR] [= ,EQ?] [+ ,PLUS] [zero? ,ZERO?] [nol? ,ZERO?] [- ,MINUS] [* ,MUL])
    ,program))))
