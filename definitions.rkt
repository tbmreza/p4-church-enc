#lang racket

(require rackunit)
(provide (all-defined-out))

(define (evalnew data)
  (eval data (make-base-namespace)))

(define (any? _) #t)
(define (procedure-at-2nd? p)
  (procedure? (second p)))

(define/contract (cnat n)
  (-> number? procedure?)
  (define (h n acc)
    (match n
      [0 acc]
      [_ `(f ,(h (sub1 n) acc))]))
  (evalnew `(lambda (f) (lambda (x) ,(h n 'x)))))

(define (unary? prim) (member prim '(add1 sub1 null? zero? not car cdr)))
(define (binary? prim) (member prim '(+ - * = cons)))

(define U (lambda (x) (x x)))
(define Y (U (λ (y) (λ (f) (f (λ (x) (((y y) f) x)))))))

(define (SUCC cn)
  (lambda (f)
    (lambda (x) (f ((cn f) x)))))

(define (PLUS cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) ((cn f) ((ck f) x))))))

(define (MUL cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) ((cn (ck f)) x)))))

(define (POW cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) (((cn ck) f) x)))))

(define TRUE   (lambda (a) (lambda (_) a)))
(define FALSE  (lambda (_) (lambda (b) b)))

(define NULL? (λ (lst) ((lst (λ (_) (λ (_) FALSE))) (λ (_) TRUE))))

(define CONS (lambda (head)
                (lambda (tail)
                  (lambda (when-cons)
                    (lambda (_) ((when-cons head) tail))))))

(define VOID  (λ (void) void))
(define NIL   (λ (when-cons) (λ (when-nil) (when-nil VOID))))

(define ERROR (λ (_)
                 ((λ (f) (f f)) (λ (f) (f f)))))

(define CAR (λ (lst)
               ((lst (λ (car) (λ (_cdr) car)))
                ERROR)))

(define CDR (λ (lst)
               ((lst (λ (_car) (λ (cdr) cdr)))
                ERROR)))

;; staging for PRED

(define c0 (lambda (_) (lambda (x) x)))
(define c1 (lambda (f) (lambda (x) (f x))))
(define c2 (lambda (f) (lambda (x) (f (f x)))))
(define c3 (lambda (f) (lambda (x) (f (f (f x))))))
(define c4 (lambda (f) (lambda (x) (f (f (f (f x)))))))
(define c5 (lambda (f) (lambda (x) (f (f (f (f (f x))))))))
(define c10 ((MUL c2) c5))
(define c100 ((MUL ((MUL c2) c2)) ((MUL c5) c5)))
