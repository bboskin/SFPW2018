#lang racket

(require syntax/parse (for-syntax syntax/parse)
         "new-mk.rkt")

(provide (for-syntax condpify))

(struct Anything [])

(define-syntax (collect-matches-conde stx)
  (syntax-parse stx
    #:literals (conde)
    [(_ x n (conde)) #''()]
    [(_ x n (conde g0 g ...))
     #'(let ([matches (collect-matches-line x g0)])
         (cons (cons n (if (null? matches) (list (Anything)) matches))
               (collect-matches-conde x (add1 n) (conde g ...))))]))

(define-syntax (collect-matches-line stx)
  (syntax-parse stx
    #:literals (conde fresh == succeed fail)
    [(_ x ()) #''()]
    [(_ x ((== a:id b:id) g ...))
     #'(collect-matches-line x (g ...))]
    [(_ x succeed g ...)
     #'(collect-matches-line x (g ...))]
    [(_ x fail g ...) #''()]
    [(_ x ((== a:id b) g ...))
     #'(if (eqv? x 'a)
           (cons 'b (collect-matches-line x (g ...)))
           (collect-matches-line x (g ...)))]
    [(_ x ((== a b:id) g ...))
     #'(if (eqv? x 'b)
           (cons 'a (collect-matches-line x (g ...)))
           (collect-matches-line x (g ...)))]
    [(_ x ((== a b) g ...))
     #'(collect-matches-line x (g ...))]
    [(_ x ((fresh (y z ...) g0 ...) g ...))
     #'(collect-matches-line x (g0 ... g ...))]
    [(_ x (g0 g ...))
     #'(collect-matches-line x (g ...))]))

(define (clean e0)
  (match e0
    [`(quote ,e)
     (displayln e0)
     (cons e (lambda (x) (equal? x e)))]
    [(? number?)
     (cons e0 (lambda (x) (equal? x e0)))]
    [(? boolean?)
     (cons e0 (lambda (x) (equal? x e0)))]
    [(? null?) (cons '() (lambda (x) (null? x)))]
    [(? pair?)
     (let ([pr1 (clean (car e0))]
           [pr2 (clean (cdr e0))])
       (cons (cons (car pr1) (car pr2))
             (lambda (x) (and (pair? x)
                              ((cdr pr1) (car x))
                              ((cdr pr2) (cdr x))))))]
    [else (cons 'Anything (lambda (x) #t))]))

(define (add-ln v ln hs)
  (if (hash-has-key? hs (car v))
      (hash-update hs (car v)
                   (lambda (l) (cons (cons ln (car l))
                                     (cdr l))))
      (hash-set hs (car v) (cons `(,ln) (cdr v)))))

(define (group-matches hs ls)
  (match ls
    ['() (hash->list hs)]
    [`((,ln ,pattern) . ,d)
     (group-matches
      (add-ln (clean pattern) ln hs)
      d)]
    [`((,ln ,pattern ...) . ,d)
     (group-matches
      (add-ln (clean pattern) ln hs)
      d)]))

(define (make-function base f ls)
  (match ls
    ['()
     (lambda (x)
       (if (var? x)
           (begin (displayln (list "in base case with" x)) base)
           (f x)))]
    [`((,ig ,ln . ,pred?) . ,d)
     (make-function
      base
      (lambda (x)
        (cond
          ((pred? x) (begin
                       (displayln
                        (list "in case with" x "returning" ln))
                       ln))
          (else (f x))))
      d)]))


(define-syntax (condpify-help stx)
  (syntax-parse stx
      #:literals (conde)
      [(_ lines () ()
          (conde (g0 g ...) ...)
          (always ...)
          (maybe ...))
       #'(new-condp (always ...)
                    (maybe ...)
                    (g0 g ...) ...)]
      [(_ lines () (x0 x ...)
          (conde g ...)
          (always ...)
          (maybe ...))
       #'(let ([sugg-x0
                (make-function
                 lines
                 (lambda (z) '())
                 (group-matches
                  (hash)
                  (collect-matches-conde x0 0 (conde g ...))))])
           (condpify-help
            lines () (x ...)
            (conde g ...)
            (always ...)
            ((sugg-x0 x0) maybe ...)))]
      [(_ lines (x0 x ...) maybes
          (conde g ...)
          (always ...)
          (maybe ...))
       #'(let ([sugg-x0
                (make-function
                 '(use-maybe)
                 (lambda (z) '())
                 (group-matches
                  (hash)
                  (collect-matches-conde x0 0 (conde g ...))))])
           (condpify-help lines (x ...) maybes
                          (conde g ...)
                          ((sugg-x0 x0) always ...)
                          (maybe ...)))]))

(define-syntax condpify
  (syntax-rules (conde)
    ((_ (always ...) (maybe ...) (conde (g0 g ...) ...))
     (let ([lines (build-list (length `(g0 ...)) (λ (x) x))])
       (condpify-help
          lines
          (always ...)
          (always ...)
          (conde (g0 g ...) ...)
          () ())))))
#;
(defrel (appendo l1 l2 o)
  (condpify
   (l1) ()
   (conde
     ((== l1 '()) (== l2 o))
     ((fresh (a d res)
        (== l1 `(,a . ,d))
        (== o `(,a . ,res))
        (appendo d l2 res))))))

#;
(defrel (valofo exp o)
  (conde
    [(== exp 'zero) (== o 'zero)]
    [(fresh (n res)
       (== exp `(add1 ,n))
       (== o `(add1 ,res))
       (valofo n res))]
    [(fresh (n)
       (== exp `(sub1 ,n))
       (valofo n `(add1 ,o)))]))
#;
(defrel (valofo exp o)
  (condpify
   (exp) (o)
   (conde
     [(== exp 'zero) (== o 'zero)]
     [(fresh (n res)
        (== exp `(add1 ,n))
        (== o `(add1 ,res))
        (valofo n res))]
     [(fresh (n)
        (== exp `(sub1 ,n))
        (valofo n `(add1 ,o)))])))
  
#;
(run 3 q (valofo q 'zero))
#;(run* (q r) (appendo q '(3) '(1 2 3)))
