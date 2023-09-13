#lang racket

(require rackunit)

;; Assignment 4: A church-compiler for Scheme, to Lambda-calculus

(provide church-compile
         ; provided conversions:
         church->nat
         church->bool
         church->listof)


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

(define c0 (lambda (_) (lambda (x) x)))
(define c1 (lambda (f) (lambda (x) (f x))))
(define c2 (lambda (f) (lambda (x) (f (f x)))))
(define c3 (lambda (f) (lambda (x) (f (f (f x))))))
(check-equal? (church->nat c0) 0)
(check-equal? (church->nat c1) 1)
(check-equal? (church->nat c2) 2)
(check-equal? (church->nat c3) 3)

; A church-encoded bool is a function taking a true-thunk and false-thunk,
;   returning (true-thunk) when true, and (false-thunk) when false
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

(define/contract (cnat n caller)
(-> number? string? procedure?)
; (define (cnat n caller)
  (define (fmt) (display "cnat caller: ") (displayln caller))
  (if (not (equal? caller "")) (fmt) (void))
  ; (display "num: ") (displayln n)
  
  (define (h n acc)
    (match n
      [0 acc]
      [_ `(f ,(h (sub1 n) acc))]))
  (eval `(lambda (f) (lambda (x) ,(h n 'x))) (make-base-namespace)))

(check-equal? (church->nat (cnat 3 "")) (church->nat (lambda (f) (lambda (x) (f (f (f x)))))))
(check-equal? (church->nat (cnat 2 "")) (church->nat (lambda (f) (lambda (x) (f (f x))))))
(check-equal? (church->nat (cnat 0 "")) (church->nat (lambda (_) (lambda (x) x))))

(define (csucc cn)
  (lambda (f)
    (lambda (x) (f ((cn f) x)))))
(check-equal? (church->nat (csucc (lambda (_) (lambda (x) x)))) (church->nat (lambda (f) (lambda (x) (f x)))))
(check-equal? (church->nat (csucc (lambda (f) (lambda (x) (f (f x)))))) (church->nat (lambda (f) (lambda (x) (f (f (f x)))))))

(define (cplus cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) ((cn f) ((ck f) x))))))
(check-equal? (church->nat ((cplus c2) c3)) 5)

; https://en.wikipedia.org/wiki/Church_encoding#Represent_the_list_using_right_fold
; 
; church pair defs:
(define cpair    (λ (a) (λ (b) (λ (n) (n (a b))))))
(define cfirst   (λ (p) (p (λ (x) (λ (y) x)))))
(define csecond  (λ (p) (p (λ (x) (λ (y) y)))))
(check-eq? (church->nat (cfirst ((cpair c0) c3))) (church->nat (cfirst ((cpair c0) c2))))
(check-eq? (church->nat (csecond ((cpair c1) c2))) (church->nat (csecond ((cpair c0) c2))))
;
; right fold functions:
(define (ccons a b)  (λ (c) (λ (n) (c a b))))
; (define (ccons2 a b) ((ccons a) b))
(define cnil         (λ (c) (λ (n) (n))))
(define cnil?        (λ (l) ((l (λ (a b) #f)) (λ () #t))))
(define ccar         (λ (l) ((l (λ (a b) a))  (λ () #f))))

(check-true (cnil? cnil))
(check-false (cnil? (ccons cnil cnil)))
(check-false (cnil? (ccons 2 cnil)))
(check-false ((ccar (ccons not cnil)) #t))

; (define nat90 (cnat 90 ""))

; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)
(define (churchify e)
  (match e
         [`(cons ,e1 '())               (ccons (cnat e1 "") cnil)]
         ; [`(cons ,e1 '())               ((?? nat90) cnull)]
         ; [`(cons ,e1 ,e2)               ((?? (cnat e1 "")) (churchify e2))]
         [(? number? e)                 (cnat e "")]
         [`(+ ,e1 ,e2)                  ((cplus (churchify e1)) (churchify e2))]
         [`(add1 ,(? number? operand))  (csucc (cnat operand ""))]
         [`(add1 ,inner)                (csucc (churchify inner))]
         [_                             e]))

; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (define todo `(lambda (x) x))
  (churchify program))
  ; (churchify
  ;  `(let ([add1 ,todo]
  ;         [+ ,todo]
  ;         [* ,todo]
  ;         [zero? ,todo])
  ;     ,program)))

