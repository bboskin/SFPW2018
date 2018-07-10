#lang racket

(require "mk.rkt"
         "pie.rkt")


;; First round of tests, without using claim/define
(time
 (run 1 (q r) 
   (pie `((add1 (add1 ,q)))
     `((the Nat ,r)))))

(time
 (run 1 q
   (pie 
    '(((the (Π ([x (Σ ([x Nat]) 
                     (= Nat x x))])
              Nat)
            (λ (pr)
              (car pr)))
            (the (Σ ([x Nat]) 
                   (= Nat x x))
              (cons (add1 (add1 zero))
                (same (add1 (add1 zero)))))))
       q)))

(time
 (run 1 (q) 
   (pie `(((the (Π ([x Nat])
                  Atom)
             (λ (n) 
               'hello))
          (car ,q)))
      `((the Atom 'hello)))))

(time
 (run 1 (T) 
   (pie `(((the ,T 
             (λ (x) x))
           (add1 zero)))
     '((the Nat (add1 zero))))))

; Second round of tests, performing more interesting syntheses

(time
  (run 1 (f)
   (pie `((claim/define foo
            (Π ([X U]) 
              (Π ([x X])
                X))
            (λ (X)
              (λ (x) x)))
          (claim/define bar
            (Π ([X U]) 
              (Π ([x X]) X))
                ,f)
          (claim/define foo=bar
            (Π ([Z U])
              (Π ([z Z])
                (= Z ((foo Z) z)
                  ((bar Z) z))))
            (λ (A)
              (λ (a)
                (same a)))))
     '())))

(time
 (run 1 (f pf)
   (pie `((claim/define f
            (Π ([n Nat])
              (Π ([m Nat])
                Nat))
             ,f)
          (claim/define f-comm
            (Π ([n Nat])
              (Π ([m Nat])
                (= Nat ((f n) m)
                  ((f m) n))))
            ,pf))
     '())))

(time
 (run 1 (base)
   (pie `((claim/define +
            (Π ([n Nat])
              (Π ([m Nat])
                Nat))
            (λ (n)
              (λ (m)
                (ind-Nat n
                  (λ (n) Nat)
                  ,base
                  (λ (x)
                    (λ (res) (add1 res)))))))
          (claim/define +-zero-l
            (Π ([n Nat])
              (= Nat n ((+ zero) n)))
            (λ (n) (same n))))
       '())))


