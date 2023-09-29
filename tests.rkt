#lang racket

(require "definitions.rkt" "church-compile.rkt" rackunit)

(check-true (church->boolean (NOT FALSE)))
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
(check-eq? 13 (church->nat (churchify `(let ([ignore 13][sub1 ,PRED]) ((lambda (num) (num 14)) (lambda (x) (sub1 x)))))))
(check-eq? 4 (church->nat ((churchify `(let ([add1 ,SUCC]) (lambda (lst) (add1 lst)))) c3)))
(check-eq? 27 (church->nat (churchify `(let ([b 3][* ,MUL]) (* b (* b 3))))))


; let expr returns usable lambda.
(check-eq? 23 (church->nat ((churchify      `(let ([ignored 13]) (lambda (lst) 23))) c0)))
(check-eq? 23 (church->nat ((church-compile `(let ([ignored 13]) (lambda (lst) 23))) c0)))

; church-compile helper propagates to els branch in lambda body.
(check-eq? 3 (church->nat (church-compile
  `(let ([len (lambda (int) (if (null? int) int (succ int)))])
     (len 2)))))

; let* can invoke in els a lambda defined in previous square bracket.
(check-eq? 7 (church->nat (church-compile
  `(let* ([len  (lambda (ignore) 7)]
	  [f    (lambda (x) (if #f 0 (len x)))])
     (f 3)))))

; curried bind-map val
(check-eq? 3 (church->nat (church-compile
  `(let ([len (lambda (succ) (lambda (int) (if (null? int) int (succ int))))])
     ((len ,SUCC) 2)))))

; binary lambda body
(check-eq? 8 (church->nat (church-compile
  `(let* ([f0   (lambda (passed) (* 2 passed))]
	  [f    (lambda (x) (if #f 0 (f0 x)))])
     (f 4)))))
