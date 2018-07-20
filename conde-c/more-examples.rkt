#lang racket

(require "mk.rkt"
         "pie.rkt")


(time 
 (run 1 (type)
      (pie `((claim/define +
                           ,type
                           (λ (n)
                             (λ (m)
                               (ind-Nat n
                                        (λ (z) Nat)
                                        m
                                        (λ (n-1) (λ (res) (add1 res)))))))
             (claim/define +-zero-r
                           (Π ([n Nat])
                              (= Nat n
                                 ((+ n) zero)))
                           (λ (n)
                             (ind-Nat n
                                      (λ (n) (= Nat n ((+ n) zero)))
                                      (same zero)
                                      (λ (n-1)
                                        (λ (IH)
                                          (ind-= IH
                                                 (λ (?) (λ (_) (= Nat (add1 n-1) (add1 ?))))
                                                 (same (add1 n-1)))))))))
              '())))



(time 
 (run 1 (fun)
      (pie `((claim/define +
                           (Π ([n Nat])
                              (Π ([m Nat])
                                 Nat))
                           (λ (n)
                             (λ (m)
                               ,fun)))
             
             (claim/define +-zero-r
                           (Π ([n Nat])
                              (= Nat n
                                 ((+ n) zero)))
                           (λ (n)
                             (ind-Nat n
                                      (λ (n) (= Nat n ((+ n) zero)))
                                      (same zero)
                                      (λ (n-1)
                                        (λ (IH)
                                          (ind-= IH
                                                 (λ (?) (λ (_) (= Nat (add1 n-1) (add1 ?))))
                                                 (same (add1 n-1)))))))))
           '())))


(time 
 (run 1 (fun)
      (pie `((claim/define +
                           (Π ([n Nat])
                              (Π ([m Nat])
                                 Nat))
                           (λ (n)
                             (λ (m)
                               (ind-Nat n
                                        (λ (z) Nat)
                                        m
                                        (λ (n-1) (λ (res) (add1 res)))))))
             
             (claim/define +-zero-r
                           (Π ([n Nat])
                              (= Nat n
                                 ((+ n) zero)))
                           (λ (n)
                             (ind-Nat n
                                      (λ (n) (= Nat n ((+ n) zero)))
                                      (same zero)
                                      (λ (n-1)
                                        (λ (IH)
                                          (ind-= IH
                                                 (λ (?) (λ (_) (= Nat (add1 n-1) (add1 ?))))
                                                 (same (add1 n-1)))))))))
              '())))
