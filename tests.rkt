#lang racket

(require "definitions.rkt" "church-compile.rkt" rackunit)

(check-true (church->boolean (NOT FALSE)))
(check-false (church->boolean (ZERO? (lambda (f) (lambda (x) (f x))))))
(check-true (church->boolean (ZERO? (lambda (_) (lambda (x) x)))))
(check-true ((church->bool TRUE) '()))
(check-false (church->boolean (NULL? ((CONS NIL) NIL))))
(check-eq? 100 (church->nat c100))
(check-equal? (church->nat (cnat 3)) (church->nat (lambda (f) (lambda (x) (f (f (f x)))))))
(check-false (church->boolean (churchify `(let ([not ,NOT])(not #t)))))
(check-false ((church->bool (churchify `(let ([not ,NOT])(not #t)))) '()))
(check-eq? 2 (church->nat (churchify `(if #t 2 3)))) ;-> c2
(check-true (church->boolean (churchify `(if #t #t #f))))
(check-equal? (church->nat (SUCC (lambda (_) (lambda (x) x)))) (church->nat (lambda (f) (lambda (x) (f x)))))
(check-equal? (church->nat ((PLUS c2) c3)) 5)
(check-equal? (church->nat ((MUL c3) c3)) 9)
(check-equal? (church->nat ((POW c3) c2)) 8)
(check-equal? ((church->listof church->nat) (CAR ((CONS ((CONS c2) ((CONS c3) NIL))) NIL))) '(2 3))
(check-eq? (church->nat ((MINUS c4) c3)) 1)
(check-true (church->boolean (churchify `(let ([not ,NOT]) (not #f)))))
(check-eq? 6 (church->nat (churchify `(let ([* ,MUL]) (* 2 3)))))
(check-eq? 4 (church->nat (churchify `(let () (if #t 4 3)))))
(check-eq? 3 (church->nat (churchify `(let ([not ,NOT]) (if (not #f) 3 5)))))
(check-eq? 12 (church->nat (churchify `(let ([b 3][* ,MUL]) (* b 4)))))
(check-eq? 27 (church->nat (churchify `(let ([b 3][* ,MUL]) (* b (* b 3))))))
(check-eq? 13 (church->nat (churchify `(let ([ignore 13][sub1 ,PRED]) ((lambda (num) (num 14)) (lambda (x) (sub1 x)))))))
(check-eq? 23 (church->nat ((churchify `(let ([ignored 13]) (lambda (lst) 23))) c0)))
(check-eq? 4 (church->nat ((churchify `(let ([add1 ,SUCC]) (lambda (lst) (add1 lst)))) c3)))
(check-eq? 3 (church->nat (church-compile
  `(let ([len (lambda (lst) (if (null? lst) lst (add1 lst)))])
     (len 2)))))

; (define ((church->listof T) c-lst)
;   ; when it's a pair, convert the element with T, and the tail with (church->listof T)
;   ((c-lst (lambda (a) (lambda (b) (cons (T a) ((church->listof T) b)))))
;    ; when it's null, return Racket's null
;    (lambda (_) '())))
;
; (define c0 (lambda (_) (lambda (x) x)))
; (define c1 (lambda (f) (lambda (x) (f x))))
; (define c2 (lambda (f) (lambda (x) (f (f x)))))
; (define c3 (lambda (f) (lambda (x) (f (f (f x))))))
; (define (church->nat c-nat)
;   ((c-nat add1) 0))
;
;
;
;
;
;
; ; '() = (λ (when-cons) (λ (when-null) (when-null)))
; (define NULL (λ (_) (λ (when-null) (when-null))))
;
; ; (cons a b) = (λ (when-cons) (λ (when-null) (when-cons a b)))
; ; old cons
; ; (define CONS (λ (a) (λ (b) (λ (when-cons) (λ (_) (when-cons a b)))))) ; curry attempt 1
; ; (define (CONS a b) (λ (when-cons) (λ (_) (when-cons a b)))) ; uncurried
;
; ; #lang racket
; ; ((λ (x y)                 (+ x y)) 3 4)
; ; ;; is equivalent to
; ; (((λ (x)           (λ (y) (+ x y))) 3) 4)
; ; (((lambda (x) (lambda (y) (+ x y))) 3) 4)
;
;
; ; (define CONS (λ (a) (λ (b) (λ (s) ((s a) b)))))
;
; ; This code from the slide assumes different application order for some
; ; reason, hence the extra pair of parens.
; ; church:null? = (λ (lst) 
; ;  (lst (λ (a b) #f)
; ;  (λ () #t)))
; ; (define NULL?        (λ (lst) ((lst (λ (_a _b) #f)) (λ () #t))))
;
; ; (check-true (NULL? NULL))
; ; old cons
; ; (check-false (NULL? (CONS c1 NULL)))
; ; (check-false (NULL? ((CONS c1) NULL)))
;
; (define TRUE  (lambda (a) (lambda (_) a)))
; (define FALSE  (lambda (_) (lambda (b) b)))
; ; (define CAR   (λ (p) (p TRUE)))
; (define ccar         (λ (lst) ((lst (λ (a _b) a))  (λ () '()))))  ; doesn't matter what I put in the last lambda body?
; (define ccdr         (λ (lst) ((lst (λ (_a b) b))  (λ () '()))))
;
; ; ; old cons
; ; ; retrieve first element
; ; (check-eq? (church->nat (ccar ((CONS c2) NULL))) 2)
; ; ; pair is not a null
; ; (check-false (NULL? ((CONS NULL) NULL)))
; ; ; retrieve second element
; ; (check-eq? (church->nat (ccdr ((CONS c2) c3))) 3)
;
; (define unchurch (church->listof church->nat))
; ; (unchurch ((CONS c1) c0))
;
; ; (check-false (NULL? ((CONS c1) c0)))
; ; ((CONS c1) c0)
;
;
;
;
;
; ; (define VOID  `(λ (void) void))
; (define VOID  (λ (void) void))
; ; (define NIL `(λ (on-cons)
; (define NIL (λ (on-cons)
;                (λ (on-nil)
;                  ; (on-nil ,VOID))))
;                  (on-nil VOID))))
;
; (define CONS (λ (head)
;                 (λ (tail)
;                   (λ (on-cons)
;                     (λ (_) ((on-cons head) tail))))))
; ; PICKUP how does PRED look like going from this CONS?
; ; STAGING
; ; (define ERROR '(λ (_)
; (define ERROR (λ (_)
;                  ((λ (f) (f f)) (λ (f) (f f)))))
; (define CAR (λ (list)
;                ((list (λ (car)
;                        (λ (_cdr)
;                          car)))
;                 ERROR)))
;
; (define CDR (λ (list)
;                ((list (λ (_car)
;                        (λ (cdr)
;                          cdr)))
;                 ERROR)))
;
; (define NULL? (λ (lst) ((lst (λ (_) (λ (_) FALSE))) (λ (_) TRUE))))
;
; ; listof
; (define (listify f church-list)
;   ((church-list
;     (λ (car) (λ (cdr) (cons (f car) (listify f cdr)))))
;    (λ (_) '())))
;
; (define (evalnew data)
;   (eval data (make-base-namespace)))
;
; (define l0 ((CONS c1) NIL))
; ; ((evalnew CAR) l0)
; ; (CAR l0)
;
; ; ; ok
; ; (listify church->nat l0)
;
;
; ; STAGING
;
; ; PICKUP migrate and delete
; (provide CONS NIL NULL? CAR CDR)
