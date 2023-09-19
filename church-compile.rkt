#lang racket

(require rackunit)
;; Assignment 4: A church-compiler for Scheme, to Lambda-calculus

(provide church-compile
         church->boolean
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
(define c4 (lambda (f) (lambda (x) (f (f (f (f x)))))))
(define c5 (lambda (f) (lambda (x) (f (f (f (f (f x))))))))

(define (evalnew data)
  (eval data (make-base-namespace)))

; A church-encoded bool is a function taking a true-thunk and false-thunk,
;   returning (true-thunk) when true, and (false-thunk) when false
(define (church->bool c-bool)
  ((c-bool (lambda (_) #t)) (lambda (_) #f)))
; PICKUP our FALSE doesn't check out with this. but what does?
; is this an if-statement evaluator?
; (church->bool  (λ (p) (p (λ (x) (λ (y) x)))))
; (church->bool (lambda (t f) t))
; (church->bool (lambda (a) (lambda (_) a)))
; (church->bool (lambda (_) #t))

(define (church->boolean tf)
  ((tf #t) #f))

(require "lists.rkt")
(check-false (church->boolean (NULL? ((CONS NIL) NIL))))

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

(define/contract (cnat n _caller)
(-> number? string? procedure?)
  (define (h n acc)
    (match n
      [0 acc]
      [_ `(f ,(h (sub1 n) acc))]))
  (eval `(lambda (f) (lambda (x) ,(h n 'x))) (make-base-namespace)))

(check-equal? (church->nat (cnat 3 "")) (church->nat (lambda (f) (lambda (x) (f (f (f x)))))))
(check-equal? (church->nat (cnat 2 "")) (church->nat (lambda (f) (lambda (x) (f (f x))))))
(check-equal? (church->nat (cnat 0 "")) (church->nat (lambda (_) (lambda (x) x))))

(define unary '(add1 ))
(define binary '(+ - * cons ))

(define (unary? prim) (member prim unary))
(define (binary? prim) (member prim binary))

(define U (lambda (x) (x x)))
; (define infinite-loop (U U))
(define Y (U (λ (y) (λ (f) (f (λ (x) (((y y) f) x)))))))
(define (SUCC cn)
  (lambda (f)
    (lambda (x) (f ((cn f) x)))))

(define (MUL cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) ((cn (ck f)) x)))))

; t1 perform left left on unhydrated churchified prog
; '(let ([b 4][j 1]) (* b 2))
; unhydrated: '((* b) #<procedure:c2>)
;
; (let ([x e]) e-b) ;; ((lambda (x) e-b) e)
; ((lambda (binds-x) c) binds-v)  ; ?
;  ((lambda (i) (i c1)) (lambda (i) (add1 i)))
; `((lambda (i) (i ,(lookup x))) (lambda (i) (,(lookup f) i)))
; '(let ([b 4][add1 SUCC]) (add1 b))

; x in rhs includes the *ellipsis* and the *parens*.
; Let expression as church terminal + debugging displays.

; '(add1 (add1 4))
; '(add1 (add1 (lambda (f) (lambda (x) (f x)))))
(define (make-c input)
  ; formal params are unique vars, lhs looks up values
  
  ; no need for replacement because input is churchified.
  (define unique '(add1))
  `(lambda ,unique ,input))

; (define (display-big-lhs)
;   ;                              binds-v
;   ; (define lhs   `(lambda (fn) (fn 1 2 3)))
;   ; (define c     `(lambda (a b c) (+ a (* b c))))
;   ;                      binds-k
;   ; (displayln (evalnew `(,lhs ,c))))
;
; ; (define lhs   `(lambda (fn) (fn ,SUCC ,c2)))
; ; (define c     `(lambda (add1 b) (add1 b)))
;
;   ; ; (add1 4)
;   ; (define lhs   `(lambda (fn) (fn ,SUCC ,c4)))
;   ; (define c     `(lambda (iadd1 i4) (iadd1 i4)))
;
;   (define lhs   `(lambda (fn) (fn ,SUCC ,c4)))
;   ; '(add1 (add1 4))
;   ; (define c     `(lambda (add1 i4) (add1 (add1 i4))))
;   ; (define c (make-c '(add1 (add1 4))))
;   
;   (display "display-big-lhs: "))


(define/contract (lex str)
  (-> string? list?)
  (define pat
    (pregexp (string-append
      "[\\s,\\(\\)]*"  ; ws, comma, () not captured
      "(" "[^\\s\\[\\]{}('\"`,;)]*"
      ")")))
  (define matches (regexp-match* pat str #:match-select cadr))
  (define res (filter (lambda (x) (not (equal? x ""))) matches))
  (map string->symbol res))

(check-equal? 3 (length (lex "(ad (ad b))")))

(define (unique vars)
  (remove-duplicates (lex (format "~a" vars))))

(define (mk-rhs vars)
; `(lambda (add1 b)  (add1 (add1 b))))
  `(lambda ,(unique vars) ,vars))
  ; (define unique '(add1 b))
  ; `(lambda ,unique ,c))

; '(add1 b)
(define (mk-lhs bind-map params)
  (define vals (map (lambda (x) (hash-ref bind-map x #f)) params))
  `(lambda (fn) (fn ,@vals)))

(define (ll binds c)
  ; c becomes the rhs, binds provide values via lhs
  ; (define lhs `(lambda (n) (n ,c1))) ; from binds
; (define c   `(lambda (b) (add1 b)))

  ; everything that appear in rhs gets its value from lhs.
  ; a lookup as in    `(lambda (b) (,(lookup 'add1) b)))
  ; can be expressed like this
  ; (define rhs `((lambda (ad1) (ad1 ,SUCC)) (lambda (c) (lambda (b) (c b)))))

  ; now going back to our big goal of evaluating the term
  ; '(let ([b 4][add1 SUCC]) (add1 b)),
  ; looks like there's 2 routes:
  ;   binds fold into one big lhs to invoke with input rhs
  ;   start with input rhs, expand by looking up nonterminals it contains
  ; 1st seems like currying technique, which is familiar.
  ; 2nd seems that it will give natural progression with structuring recursion for nested terms.

  ; how does a "big lhs" look like? with several variable in rhs?  ok
  ; (display-big-lhs)
  ; how does a c that makes no mention of variables look like?  ok
  ; (define constrhs   `(lambda (b) ,c2))
  ; (evalnew `(,lhs ,constrhs)))

  ; interpolate big lhs from c
  ; (define params (unique-vars c))
  ; (define big `(lambda (fn) (fn x y z)))

  ; (make-immutable-hash
  ; (map (λ (pr) (cons (first pr) (second pr))) l))

  (define (churchify-num-symbol s)
    (match s
      [(? number? s) (cnat s "")]
      [_ s]))
  
  (define (mk-map)
    (make-immutable-hash
      (map (λ (kv) (cons (first kv) (churchify-num-symbol (second kv)))) binds)))

  (define rhsnew (mk-rhs c))
  (define lhsnew (match rhsnew  [`(lambda ,params ,_)  (mk-lhs (mk-map) params)]))

  (evalnew `(,lhsnew ,rhsnew)))
  ; `(,lhsnew ,rhsnew))
  ; (evalnew `(,lhsnew ,rhs)))

  ; (evalnew `(,lhs ,rhs)))

(define (left-left2 binds c) ; takes unhydrated e  return church terminal
  (define (lookup k caller)
    ; (define (fmt) (display "lookup caller: ") (displayln caller))
    ; (if (not (equal? caller "")) (fmt) (void))

    ; (hash-ref (hash-from binds) k))
    (match k ['b c3]['c c3]['add1 SUCC]['* MUL][(? number? k) (cnat k "")][_ #f]))
  
  (define (evalfx f x)
    (evalnew `((lambda (i) (i ,(lookup x ""))) (lambda (i) (,(lookup f "") i)))))

  (define (del sub)
    ; (cook sub))
    (define f SUCC)
    (define x (church->nat (cook sub)))
    (evalnew `((lambda (i) (i ,(lookup x ""))) (lambda (i) (,f i))))
    (cook sub))

  (define (cook c)
    (match c
      [`(,f (,x ...))  (del x)]
    ; [`(,f (,x ...))  (evalfx f (cook x))]
      [`(,f ,x)        (evalfx f x)]
      [_ c3]))

  ; (cook c))

  (define (h c acc)
    acc)  ; poc you can stack evalnew on top of the other
  (h c c0))

  ; PICKUP (h c const-lambda)

  ; (define (cook fx)
  ;   (match fx
  ;     [`(,f ,x)    (match x
	; 	     [`(,xf ,xx)  `(lambda (f) (lambda (x) (f (f x))))]
	; 	     [_           `(lambda (f) (lambda (x) (f (f x))))])]
  ;     [_           `(lambda (f) (lambda (x) (f (f x))))]))
  ;
  ;     ; [`(,f ,x)    `((lambda (i) (i c1)) (cook ,f2 ,x2))]
  ;     ; [_           `((lambda (i) (i ,(lookup x))) (lambda (i) (,(lookup f) i)))]))
  ;
  ;   ; (evalnew `((lambda (i) (i ,(lookup x))) (lambda (i) (,(lookup f) i)))))
  ;
  ;     ; `((lambda (i) (i ,(lookup 'b))) (lambda (i) (,(lookup '*) i)))))
  ;
  ; (evalnew (cook c)))

  ; (match c
  ;   [`(,f ,x)  (evalnew (cook f x))]
  ;   [_ c0]))

(define (churchify e)
  ; (let ([x e]) e-b) ;; ((lambda (x) e-b) e)
  ; ( (+ (lambda (f) …)) (lambda (f) …))

  (define (def e) (display "default e=")(displayln e) e)

  (match e
  ; [`('())                          NIL]
    ['#t                             TRUE]
    ['#f                             FALSE]
    [`(if #t ,then ,_)               (churchify then)]
    [`(if #f ,_ ,els)                (churchify els)]
    [`(if ,b ,then ,els)             (churchify `(if ,(churchify b) ,then ,els))]
    [(? number? e)                   (cnat e "")]

    [`(,(? unary? fn) ,arg)          `(,fn ,(churchify arg))]
    [`(,(? binary? fn) ,arg1 '())  `((,fn ,(churchify arg1)) ,NIL)]
    [`(,(? binary? fn) ,arg1 ,arg2)  `((,fn ,(churchify arg1)) ,(churchify arg2))]
    [`(let ,binds ,e)                (ll binds (churchify e))]
    [_ e]))
    ; [_ (def e)]))

; (churchify '(let ([b 4][add1 SUCC]) (add1 b)))
; (church->nat (churchify '(let ([b 4][add1 SUCC]) (add1 b))))
; (church->nat (churchify '(let ([b 9][add1 SUCC]) (add1 (add1 b)))))

; ok
(church->nat (churchify `(let ([b 9][add1 ,SUCC]) (add1 (add1 b)))))
(church->nat (churchify `(let ([b 6][ad ,SUCC]) (ad (ad b)))))
(church->nat (churchify `(let ([b 9][* ,MUL]) (* b 2))))
(church->nat (churchify `(let ([b 4][add1 ,SUCC][* ,MUL]) (* b (add1 9)))))

(churchify '(cons 1 (cons 2 (cons 3 '()))))

; (define (SUCC cn)
;   (lambda (f)
;     (lambda (x) (f ((cn f) x)))))
(check-equal? (church->nat (SUCC (lambda (_) (lambda (x) x)))) (church->nat (lambda (f) (lambda (x) (f x)))))
(check-equal? (church->nat (SUCC (lambda (f) (lambda (x) (f (f x)))))) (church->nat (lambda (f) (lambda (x) (f (f (f x)))))))

(define (PLUS cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) ((cn f) ((ck f) x))))))
(check-equal? (church->nat ((PLUS c2) c3)) 5)

; (define (MUL cn)
;   (lambda (ck)
;     (lambda (f)
;       (lambda (x) ((cn (ck f)) x)))))
(check-equal? (church->nat ((MUL c3) c3)) 9)

(define (cpow cn)
  (lambda (ck)
    (lambda (f)
      (lambda (x) (((cn ck) f) x)))))
(check-equal? (church->nat ((cpow c3) c3)) 27)

; gh, wiki
(define TRUE   (lambda (a) (lambda (_) a)))
(define FALSE  (lambda (_) (lambda (b) b)))
(define NOT    (λ (b) ((b FALSE) TRUE)))
; what gets applied with TRUE and gives #t
; ((lambda (fn) (fn #t))   (lambda (x)  (x (x ,c0))))

(define ccar         (λ (l) ((l (λ (a b) a))  (λ () #f))))
(define cnil?        (λ (l) ((l (λ (a b) #f)) (λ () #t))))  ; from slide
(define cnil         (λ (c) (λ (n) (n))))

; (cons a b) = (λ (when-cons) (λ (when-null) (when-cons a b)))
(define (ccons a b) (λ (c) (λ (n) (c a b))))
; (define (ccons a b) (λ (n) (n a b)))

; This definition of cons dictates how unchurch should be implemented for cons-list.
; lists.rkt
(define PAIR (λ (a) (λ (b) (λ (s) ((s a) b)))))
(define CAR  (λ (p) (p TRUE)))
(define CDR  (λ (p) (p FALSE)))
; (define NIL FALSE)
; (define NIL? (λ (p) (??)))

; lists.rkt
; (check-eq? (church->nat (CAR ((PAIR c4) NIL))) 4)
(check-eq? (church->nat (CAR ((PAIR c4) FALSE))) 4)
(check-eq? (church->nat (CDR ((PAIR c4) c2))) 2)

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
(define T (λ (p) ((PAIR (SUCC (CAR p))) (CAR p))))
(define PRED (λ (n) (CDR ((n T) ((PAIR c0) c0)))))
(check-eq? (church->nat (PRED c4)) 3)

(define MINUS (lambda (m) (lambda (n) ((n PRED) m))))
(check-eq? (church->nat ((MINUS c4) c3)) 1)

; https://en.wikipedia.org/wiki/Church_encoding#Represent_the_list_using_right_fold
; 
; church pair defs:
(define cpair    (λ (a) (λ (b) (λ (n) (n (a b))))))
(define cfirst   (λ (p) (p (λ (x) (λ (y) x)))))
(define csecond  (λ (p) (p (λ (x) (λ (y) y)))))
(check-eq? (church->nat (cfirst ((cpair c0) c3))) (church->nat (cfirst ((cpair c0) c2))))
; (check-eq? (church->nat (csecond ((cpair c1) c2))) (church->nat (csecond ((cpair c0) c2))))
(check-eq? (church->nat (FALSE ((cpair c1) c2))) (church->nat (csecond ((cpair c0) c2))))
;
; right fold functions:
; (define (ccons a b) (λ (c) (λ (n) (c a b))))
; slide:
; ‘() = (λ (when-cons) (λ (when-null)
;  (when-null)))
;
; (cons a b) = (λ (when-cons) (λ (when-null) (when-cons a b)))


(check-true (cnil? cnil))
(check-false (cnil? (ccons cnil cnil)))
(check-false (cnil? (ccons c2 cnil)))
(check-false ((ccar (ccons not cnil)) #t))

(define c30 ((MUL ((MUL c3) c2)) ((PLUS c3) c2)))
; churchify recursively walks the AST and converts each expression in the input language (defined above)
;   to an equivalent (when converted back via each church->XYZ) expression in the output language (defined above)
; (define (churchify e)
;   ; (define prog '(cons 1 (cons 2 (cons 3 '()))))
;   (define (ff)
;     (displayln "correct arm")
;     (ccons c2 cnil))
;
;   ; u, w, and y combinators
;
;   ; (let ([name (lambda (x) (+ x x))]) (name 10))
;   ; ((lambda (name) (name 10)) (lambda (x) (+ x x)))
;
;   ;           a          b               c
;   ; (let   ([name (lambda (x) x)])   (name 30))
;   ; ((lambda (name) (name c30)) (lambda (x) x))
;   ;           a          c               b
;
;   (define (ss-old binds e)
;     ; (displayln binds) ; list of kv pair
;     ; (define (name x) x) (name 30)
;     ; (let   ([name    (lambda (x) x)  ])   (name 30))
;     ; ((lambda (name)     (name c30)   ) (lambda (x) x))
;
;     ; get c3, c1 from kv pairs
;
;     ; curry for each bind
;     ; (* b name)
;     ; (lambda (name) (* b name))
;     ; (lambda (b) (lambda (name) (* b name)))
;
;     ; x: how am I getting my value? well place my enclosing lambda right after name-lambda
;     ; apply the whole again to find out what's b
;
;     ; mechanism to pass one arg
;     ; now can that one appl return another lambda...
;     ; the following still gives unbound identifier...
;     ; ((lambda (b) (b c1)) ((lambda (name) (name c3) )
;     ;    (lambda (x) ((MUL b) x))))
;     ; we just need to have a reliable single bind let form. multi binds is nested let:
;     ; (define (double x) (+ x x))
;     ; (define (quadruple x) (double (double x)))
;     ; (quadruple 10)
;     ;         This could be rewritten as
;     ; (let ([double (lambda (x) (+ x x))])
;     ;   (let ([quadruple (lambda (x) (double (double x)))])
;     ;     (quadruple 10)))
;
;     ; e (add1 c2) what part of evalnew
;     ; failed but expected: rhs is identity
;     ; (lambda (x) (add1 x))
;     (displayln e)
;     (define (arm n v)
;       (evalnew
; 	; `((lambda (,n) (,n ,(churchify v)) ) ,(churchify e))))
; 	; `((lambda (,n) (,n ,(churchify v)) ) (lambda (x) ,(churchify e)))))
; 	`((lambda (,n) (,n ,(churchify v)) ) (lambda (x) x))))
;
;     (match binds
;       ; [`(,n ,v) (evalnew `((lambda (,n) (,n ,(churchify v)) ) (lambda (x) x)))]
;       [`(,n ,v) (arm n v)]
;       [_ #f])
;
;     ; (evalnew `((lambda (name) (name ,c3) ) (lambda (x) x)))
;
;     ; (* 1 x)
;     ; ; ok
;     ; ((lambda (name) (name c3) )
;     ;    (lambda (x) ((MUL c1) x)))
;
;     ; ; '(let ([name 3]) 3))  ok for static
;     ; ((lambda (name) (name (churchify e))) (lambda (x) x))
;     )
;   (define (left-left binds e)
;     (display "binds: ")(displayln binds)
;     (display "e: ")(displayln e)
;
;     ; (define k (first binds))
;     ; (define fn (second k))
;     ; ; (+ 3 2)
;     ; (define fn PLUS)
;     ; ((lambda (b) (b (churchify 5))) (lambda (i) ((fn (churchify 2)) (churchify 3))))
;
;     (define (lookup-val k)
;       (match k
;         [(? number? k)  (cnat k "")]
;         [_ c0]))
;
;     (define (body-template input-body)
;       (match input-body
;         [`(sub1 ,_)  (lambda (i) (PRED i))]
;         [`(add1 ,_)  (lambda (i) (SUCC i))]
;         ; Silently return identity lambda.
;         [_           (lambda (i) i)]))
;
;     (define (body-template2 input-body)
;       (match input-body
;         [`(add1 ,k)             
; 	  ((lambda (i) (i (lookup-val k))) (lambda (i) (SUCC i)))]
;         [`(* ,_ ,_)
; 	  ((lambda (j) (j c2)) ((lambda (b) (b c4)) (lambda (b) (MUL b))))]
;         ; Silently return identity lambda.
;         [_              (lambda (i) i)]))
;
;     
;
;     ; (add1 b)
;     ; ...match template
;     ; (lambda (b) (SUCC b))
;     ; ...lookup and build
;     ; (lambda (b) (b c0)) (lambda (b) (SUCC b))
;
;     (body-template2 e)
;
;     ; ; ok
;     ; ((lambda (j) (j c2))
;     ; ;  passer
;     ; ((lambda (b) (b c4)) (lambda (b) (MUL b))))
;     ; ;   passer                 template
;
;     ; ; ok
;     ; ((lookup-val 'b)      (body-template e))
;
;     ; (+ b j)
;     ; applying here means prefexing a lambda whose body is a looked up value.
;     ; (SUCC b)       (lambda (b) (b val)) (lambda (b) (fn b))
;     ; ((PLUS b) j)   (lambda (j) (j val)) (...)
;
;     ; (define jval (churchify 1))
;     ; (define bval (churchify 5))
;     ; (define fn PLUS)
;     ; ((lambda (j) (j jval))
;     ;  ((lambda (b) (b bval)) (lambda (b) (fn b))))
;
;     ; ; (add1 b)
;     ; (define fn SUCC)
;     ; ; ((lambda (b) (b (churchify 4))) (lambda (i) (fn i)))
;     ; ((lambda (b) (b (churchify 4))) (lambda (i) (fn i)))
;
;     ; (add1 2)
;     ; (define fn SUCC)
;     ; ((lambda (b) (b (churchify 2))) (lambda (i) (fn (churchify 2))))
;
;     ; c3
;
;     ; replace occurrences of ,k in rhs lambda??
;     ; good for '(tambah1 (tambah1 0))
;     ; (evalnew `((lambda (,k) (,k ,fn))   (lambda (x)  (x (x ,c0)))))
;     ; ; good for '(tambah1 4)
;     ; (evalnew `((lambda (,k) (,k ,fn)) (lambda (x)  (x ,c4))))
;     ; ; good for '3
;     ; (evalnew `((lambda (,k) (,k ,fn)) (lambda (x)  ,c3)))
;     )
;
;   (define (default-arm e) (displayln "default arm...") e)
;
;   (match e
; 	 ; racket doesn't allow (quote ()) as pattern?
;          [`(cons ,e1 '())               ((CONS (churchify e1)) NIL)]
;          [`(cons ,e1 ,e2)               ((CONS (churchify e1)) (churchify e2))]
;          [`(null? ,inner)               (NULL? (churchify inner))]
;
;          ['#t                           TRUE]
;          ['#f                           FALSE]
;          [`(not ,b)                     (NOT (churchify b))]
;          [`(if #t ,then ,_)             (churchify then)]
;          [`(if #f ,_ ,els)              (churchify els)]
;          [`(if ,b ,then ,els)           (churchify `(if ,(churchify b) ,then ,els))]
;
;          [(? number? e)                 (cnat e "")]
;          [`(+ ,e1 ,e2)                  ((PLUS (churchify e1)) (churchify e2))]
;          [`(- ,e1 ,e2)                  ((MINUS (churchify e1)) (churchify e2))]
;          [`(* ,e1 ,e2)                  ((MUL (churchify e1)) (churchify e2))]
; 	 [`(sub1 ,inner)                (PRED (churchify inner))]
;          [`(add1 ,inner)                (SUCC (churchify inner))]
;          ; [`(,(? unary? fn) ,inner)    `(fn ,(churchify inner))]
;
;          [`(let ,binds ,e)             (left-left binds e)  ]
;
;          ; [_                             e]))
;          [_                             (default-arm e)]))

; Takes a whole program in the input language, and converts it into an equivalent program in lambda-calc
; Build a let expression containing all helpers and the input program.
; Delegate the expression to churchify.
(define (church-compile program)
  ; Define primitive operations and needed helpers using a top-level let form?
  (churchify
   `(let ([add1 ,SUCC]
          [cons ,CONS]
          [+ ,PLUS]
          [- ,MINUS]
          [* ,MUL])
      ,program)))
