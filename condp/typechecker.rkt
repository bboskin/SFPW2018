#lang racket

(require "mk.rkt"
         "helpers.rkt"
         "substitution.rkt"
         "normalize.rkt")

(provide synth
         check
         type
         ≡-type
         ≡)

;; helpers for synth

(defrel ((synth-simple e T) Γ exp o)
  (== exp e)
  (== o `(the ,T ,e)))

(defrel (synth-var Γ exp o)
  (non-reserved-Pie-symbol exp)
  (fresh (τ-v τ v)
    (apply-Γ Γ exp τ-v)
    (read-back-typo Γ τ-v τ)
    (conde
      [(fresh (v v-v)
         (apply-ρ Γ exp v-v)
         (read-backo Γ τ-v v-v v)
         (== o `(the ,τ ,v)))]
      [(free-in-ρ exp Γ)
       (== o `(the ,τ ,exp))])))

(defrel (synth-the Γ exp o)
  (fresh (τ e τo eo)
    (== exp `(the ,τ ,e))
    (== o `(the ,τo ,eo))
    (type Γ τ τo)
    (check Γ e τo eo)))

(defrel (synth-quote Γ exp o)
  (fresh (s)
    (== exp `(quote ,s))
    (symbolo s)
    (== o `(the Atom (quote ,s)))))

(defrel (synth-add1 Γ exp o)
  (fresh (n no)
    (== exp `(add1 ,n))
    (== o `(the Nat (add1 ,no)))
    (check Γ n 'Nat no)))

(defrel (synth-ind-Nat Γ exp o)
  (fresh (t m b s to mo bo so τb vars k τk1 τk2 τf τf-v norm ρ)
    (== exp `(ind-Nat ,t ,m ,b ,s))
    (== o `(the ,τf ,norm))
    (check Γ t 'Nat to)
    (check Γ m '(Π ([_ Nat]) U) mo)
    (normalizo Γ 'UNIVERSE `(,mo zero) τb)
    (check Γ b τb bo)
    (just-names Γ vars)
    (freshen 'k vars k)
    (extend-ρ Γ k `(NEU NAT (VAR ,k)) ρ)
    (normalizo ρ 'UNIVERSE `(,mo ,k) τk1)
    (normalizo ρ 'UNIVERSE `(,mo (add1 ,k)) τk2)
    (check Γ s `(Π ([,k Nat]) (Π ([_ ,τk1]) ,τk2)) so)
    (valofo Γ `(,mo ,to) τf-v)
    (read-back-typo Γ τf-v τf)
    (normalizo Γ τf-v `(ind-Nat ,to ,mo (the ,τb ,bo) ,so) norm)))

(defrel ((synth-dep-binder tag) Γ exp o)
  (fresh (x A D Ao Γ^ Do Ao-v)
    (== exp `(,tag ([,x ,A]) ,D))
    (non-reserved-Pie-symbol x)
    (== o `(the U (,tag ([,x ,Ao]) ,Do)))
    (check Γ A 'U Ao)
    (valofo Γ Ao Ao-v)
    (extend-Γ Γ x Ao-v Γ^)
    (check Γ^ D 'U Do)))

(defrel (synth-car Γ exp o)
  (fresh (pr x A D prₒ norm τ-A)
    (== exp `(car ,pr))
    (== o `(the ,A ,norm))
    (synth Γ pr `(the (Σ ([,x ,A]) ,D) ,prₒ))
    (valofo Γ A τ-A)
    (normalizo Γ τ-A `(car ,prₒ) norm)))

(defrel (synth-cdr Γ exp o)
  (fresh (pr x A D prₒ D^ norm a τ-A D-v)
    (== exp `(cdr ,pr))
    (== o `(the ,D^ ,norm))
    (synth Γ pr `(the (Σ ([,x ,A]) ,D) ,prₒ))
    (valofo Γ A τ-A)
    (normalizo Γ τ-A `(car ,prₒ) a)
    (substo a x D D^)
    (valofo Γ D^ D-v)
    (normalizo Γ D-v `(cdr ,prₒ) norm)))

(defrel (synth-= Γ exp o)
  (fresh (X from to Xₒ fromₒ toₒ)
    (== exp `(= ,X ,from ,to))
    (== o `(the U (= ,Xₒ ,fromₒ ,toₒ)))
    (check Γ X 'U Xₒ)
    (check Γ from Xₒ fromₒ)
    (check Γ to Xₒ toₒ)))

(defrel (synth-ind-= Γ exp o)
  (fresh (t m b τ-norm τ-norm-v norm X from to tₒ mo bo vars x1 x2 τb)
        (== exp `(ind-= ,t ,m ,b))
        (== o `(the ,τ-norm ,norm))
        (synth Γ t `(the (= ,X ,from ,to) ,tₒ))
        (just-names Γ vars)
        (freshen 'x1 vars x1)
        (freshen 'x2 vars x2)
        (check Γ m `(Π ([,x1 ,X]) (Π ([,x2 (= ,X ,from ,x1)]) U)) mo)
        (normalizo Γ 'UNIVERSE `((,mo ,from) (same ,from)) τb)
        (check Γ b τb bo)
        (valofo Γ `((,mo ,to) ,tₒ) τ-norm-v)
        (read-back-typo Γ τ-norm-v τ-norm)
        (normalizo Γ τ-norm-v `(ind-= ,tₒ ,mo ,bo) norm)))

(defrel (synth-app Γ exp o)
  (fresh (f arg x Arg R fₒ argₒ Rₒ Rₒ-v norm)
    (== exp `(,f ,arg))
    (== o `(the ,Rₒ ,norm))
    (non-reserved-Pie-fn f)
    (non-reserved-Pie-symbol x)
    (synth Γ f `(the (Π ([,x ,Arg]) ,R) ,fₒ))
    (check Γ arg Arg argₒ)
    (substo argₒ x R Rₒ)
    (valofo Γ Rₒ Rₒ-v)
    (normalizo Γ Rₒ-v `(,fₒ ,argₒ) norm)))

;; Relevance functions for synth
(define synth-forms
  '(add1 quote the ind-Nat ind-= Π Σ = car cdr))

(define eliminators '(var car cdr app ind-Nat ind-=))


(define (complex-type? t)
  (and (pair? t)
       (member (car t) '(Π Σ =))))

(define (synth-exp-table exp)
  (match exp
    [(? simple?) `(,exp)]
    [(? symbol?) '(var)]
    [(? (exp-memv? synth-forms)) `(,(car exp))]
    [`(,rator ,rand) '(app)]
    [(? var?) '(use-out)]
    [else '()]))

(define (synth-out-table exp)
  (match exp
    [`(the ,τₑ ,e)
     (match τₑ
       [(? simple?)
        (append (get-constructors τₑ) eliminators)]
       [(? symbol?) '(var)]
       [(? complex-type?) '(the)]
       [(? var?) all-exprs])]
    [else '()]))


(defrel (synth Γ exp o)
  (condp
    ((exp synth-exp-table in-mode)
     (o synth-out-table))
    [var (synth-var Γ exp o)] ;; Hypothesis
    [the (synth-the Γ exp o)] ;; The
    [Atom ((synth-simple 'Atom 'U) Γ exp o)] ;; UI-1    
    [quote (synth-quote Γ exp o)] ;; AtomI-tick
    [Nat ((synth-simple 'Nat 'U) Γ exp o)] ;; UI-9
    [zero ((synth-simple 'zero 'Nat) Γ exp o)] ;; NatI-1
    [add1 (synth-add1 Γ exp o)] ;; NatI-2
    [ind-Nat (synth-ind-Nat Γ exp o)] ;; NatE-4
    [Trivial ((synth-simple 'Trivial 'U) Γ exp o)] ;; UI-14
    [sole ((synth-simple 'sole 'Trivial) Γ exp o)] ;; TrivI
    [Σ ((synth-dep-binder 'Σ) Γ exp o)] ;; UI-2
    [car (synth-car Γ exp o)] ;; ΣE-1
    [cdr (synth-cdr Γ exp o)] ;; ΣE-2
    [Π ((synth-dep-binder 'Π) Γ exp o)] ;; UI-5
    [= (synth-= Γ exp o)] ;; UI-12
    [ind-= (synth-ind-= Γ exp o)] ;; EQE-5
    [app (synth-app Γ exp o)])) ;; Fun-E-1 

;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;

;; helpers for check

(defrel (check-cons Γ exp τ o)
  (fresh (a d x A D aₒ Dₒ dₒ)
    (== exp `(cons ,a ,d))
    (== τ `(Σ ([,x ,A]) ,D))
    (non-reserved-Pie-symbol x)
    (== o `(cons ,aₒ ,dₒ))
    (check Γ a A aₒ)
    (substo aₒ x D Dₒ)
    (check Γ d Dₒ dₒ)))

(defrel (check-λ Γ exp τ o)
  (fresh (x r y Arg R R^ Γ^ rₒ Argᵥ)
    (== exp `(λ (,x) ,r))
    (non-reserved-Pie-symbol x)
    (== τ `(Π ([,y ,Arg]) ,R))
    (non-reserved-Pie-symbol y)
    (== o `(λ (,x) ,rₒ))
    (substo x y R R^)
    (valofo Γ Arg Argᵥ)
    (extend-Γ Γ x Argᵥ Γ^)
    (check Γ^ r R^ rₒ)))

(defrel (check-= Γ exp τ o)
  (fresh (X from to mid midₒ)
    (== exp `(same ,mid))
    (== τ `(= ,X ,from ,to))
    (== o `(same ,midₒ))
    (check Γ mid X midₒ)
    (≡ Γ X from midₒ)
    (≡ Γ X midₒ to)))

(defrel (use-switch exp)
  (conde
    [(symbolo exp)]
    [(fresh (a d)
       (== exp `(,a . ,d))
       (=/= a 'same)
       (=/= a 'λ)
       (=/= a 'cons))]))

(defrel (switch-expr Γ exp τ o)
  (fresh (t)
    (use-switch exp)
    (synth Γ exp `(the ,t ,o))
    (≡-type Γ τ t)))

(defrel (switch-τ Γ exp τ o)
  (fresh (t)
    (use-switch exp)
    (≡-type Γ τ t)
    (synth Γ exp `(the ,t ,o))))

;; Relevance functions for check

(define check-forms '(same λ cons))

(define (check-out-table₂ e)
  (match e
    [(? var?) '(same λ cons switch-expr)]
    [(? (exp-memv? check-forms)) `(,(car e) switch-τ)]
    [else '(switch-τ)]))

(define (check-out-table pr)
  (let ([τ (car pr)]
        [exprᵉ (cdr pr)])
    (match τ
      [`(= ,X ,from ,to) '(switch-τ same)]
      [`(Π ((,x ,A)) ,R) '(switch-τ λ)]
      [`(Σ ((,x ,A)) ,D) '(switch-τ cons)]
      [(? var?) (check-out-table₂ exprᵉ)]
      [else '(switch-τ)])))

(define (check-expr-table exp)
  (match exp
    [(? (exp-memv? check-forms)) `(,(car exp))]
    [(? var?) '(use-out)]
    [else '(switch-expr)]))


(defrel (check Γ exp τ o)
  (condp
    ((`(,τ . ,o) check-out-table)
     (exp check-expr-table in-mode))
    [cons (check-cons Γ exp τ o)] ;; ΣI
    [λ (check-λ Γ exp τ o)] ;; FunI-1
    [same (check-= Γ exp τ o)] ;; EqI
    [switch-expr (switch-expr Γ exp τ o)] ;; Switch
    [switch-τ (switch-τ Γ exp τ o)]))


;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;

;; helpers for type

(defrel (type-id T τ o)
  (== τ T)
  (== o T))

(defrel (type-dep-binder tag Γ τ o)
  (fresh (x Arg R Argo Ro Γ^ Argoᵥ)
    (== τ `(,tag ([,x ,Arg]) ,R))
    (== o `(,tag ([,x ,Argo]) ,Ro))
    (type Γ Arg Argo)
    (valofo Γ Argo Argoᵥ)
    (extend-Γ Γ x Argoᵥ Γ^)
    (type Γ^ R Ro)))

(defrel (type-= Γ τ o)
  (fresh (X from to Xo fromo too)
    (== τ `(= ,X ,from ,to))
    (== o `(= ,Xo ,fromo ,too))
    (type Γ X Xo)
    (check Γ from Xo fromo)
    (check Γ to Xo too)))

; Relevance function
(define (type-table type)
  (match type
    [(? simple?) `(,type)]
    [(? complex-type?) `(,(car type))]
    [(? var?) `(switch . ,(get-constructors 'U))]
    [else '(switch)]))

(defrel (type Γ τ o)
  (condp
    ((τ type-table in-mode))
    [U (type-id 'U τ o)] ;; UF
    [Nat (type-id 'Nat τ o)] ;; NatF
    [Atom (type-id 'Atom τ o)] ;; AtomF
    [Trivial (type-id 'Trivial τ o)] ;; TrivialF
    [Π (type-dep-binder 'Π Γ τ o)] ;; FunF-1
    [Σ (type-dep-binder 'Σ Γ τ o)] ;; ΣF-1
    [= (type-= Γ τ o)] ;; EQ-F
    [switch (check Γ τ 'U o)]))

;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;

;; helpers for ≡-type

(defrel (≡-type-id T e1 e2)
  (== e1 T)
  (== e2 T))

(defrel (≡-type-binder tag Γ e1 e2)
  (fresh (x A1 D1 y A2 D2 D2^ Γ^ Aᵥ)
    (== e1 `(,tag ([,x ,A1]) ,D1))
    (== e2 `(,tag ([,y ,A2]) ,D2))
    (≡-type Γ A1 A2)
    (valofo Γ A1 Aᵥ)
    (extend-Γ Γ x Aᵥ Γ^)
    (substo x y D2 D2^)
    (≡-type Γ^ D1 D2^)))

(defrel (≡-type-= Γ e1 e2)
  (fresh (X1 from1 to1 X2 from2 to2)
    (== e1 `(= ,X1 ,from1 ,to1))
    (== e2 `(= ,X2 ,from2 ,to2))
    (≡-type Γ X1 X2)
    (≡ Γ X1 from1 from2)
    (≡ Γ X1 to1 to2)))

(define (≡-type-table exp)
  (match exp
    [(? simple?) (list exp)]
    [(? complex-type?) (list (car exp))]
    [(? var?) '(switch)]
    [else '(switch)]))

(defrel (≡-type Γ e1 e2)
  (condp
    ((e1 ≡-type-table in-mode)
     (e2 ≡-type-table in-mode))
    [U (≡-type-id 'U e1 e2)] ;; USame-U
    [Nat (≡-type-id 'Nat e1 e2)] ;; NatSame-Nat
    [Atom (≡-type-id 'Atom e1 e2)] ;; AtomSame-Atom
    [Trivial (≡-type-id 'Trivial e1 e2)] ;; TrivialSame-Trivial
    [Σ (≡-type-binder 'Σ Γ e1 e2)] ;; ΣSame-Σ
    [Π (≡-type-binder 'Π Γ e1 e2)] ;; FunSame-Π
    [= (≡-type-= Γ e1 e2)] ;; EQSame-EQ
    [switch (≡ Γ 'U e1 e2)]))


;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;

;; helpers for ≡

(defrel (≡-symbol s T e1 e2 τ)
  (== e1 s) (== e2 s) (== τ T))

(defrel (≡-var Γ τ e1 e2)
  (== e1 e2)
  (symbolo e1)
  (fresh (v)
    (apply-Γ Γ e1 v)
    (read-back-typo Γ v τ)))

(defrel (≡-the Γ τ e1 e2)
  (fresh (t1 b1)
    (== e1 `(the ,t1 ,b1))
    (≡-type Γ τ t1)
    (≡ Γ τ e2 b1)))

(defrel (≡-sole Γ τ e1 e2)
  (== τ 'Trivial)
  (== e2 'sole)
  (≡ Γ 'Trivial e1 e1))

(defrel (≡-quote τ e1 e2)
  (fresh (s)
    (== e1 `(quote ,s))
    (== e2 `(quote ,s))
    (== τ 'Atom)))

(defrel (≡-dep-binder tag Γ τ e1 e2)
  (fresh (x A1 D1 y A2 D2 D2^ Γ^ Aᵥ)
    (== e1 `(,tag ([,x ,A1]) ,D1))
    (== e2 `(,tag ([,y ,A2]) ,D2))
    (== τ 'U)
    (≡ Γ 'U A1 A2)
    (valofo Γ A1 Aᵥ)
    (extend-Γ Γ x Aᵥ Γ^)
    (substo x y D2 D2^)
    (≡ Γ^ 'U D1 D2^)))

(defrel (≡-cons Γ τ e1 e2)
  (fresh (a1 d1 a2 d2 x A D D^)
    (== e1 `(cons ,a1 ,d1))
    (== e2 `(cons ,a2 ,d2))
    (== τ `(Σ ([,x ,A]) ,D))
    (≡ Γ A a1 a2)
    (substo a1 x D D^)
    (≡ Γ D^ d1 d2)))

(defrel (≡-car Γ τ e1 e2)
  (fresh (pr1 pr2 x D)
    (== e1 `(car ,pr1))
    (== e2 `(car ,pr2))
    (≡ Γ `(Σ ([,x ,τ]) ,D) pr1 pr2)))

(defrel (≡–Σ-η1 Γ τ e1 e2)
  (fresh (a d x D Γ^ τᵥ)
    (== e1 `(car (cons ,a ,d)))
    (≡ Γ τ a e2)
    (valofo Γ τ τᵥ)
    (extend-Γ Γ x τᵥ Γ^)
    (≡ Γ^ D d d)))

(defrel (≡-cdr Γ τ e1 e2)
  (fresh (pr1 pr2 a x A D A-v)
    (== e1 `(cdr ,pr1))
    (== e2 `(cdr ,pr2))
    (≡ Γ `(Σ ([,x ,A]) ,D) pr1 pr2)
    (valofo Γ A A-v)
    (normalizo Γ A-v `(car ,pr1) a)
    (substo a x D τ)))

(defrel (≡–Σ-η2 Γ τ e1 e2)
  (fresh (a1 d a2 x A Aᵥ D Γ^)
    (== e1 `(cdr (cons ,a1 ,d)))
    (≡ Γ A a1 a2)
    (valofo Γ A Aᵥ)
    (extend-Γ Γ x Aᵥ Γ^)
    (≡ Γ^ D d e2)
    (substo a2 x D τ)))

(defrel (≡-Σ-η Γ τ e1 e2)
  (fresh (pr2)
    (== e2 `(cons (car ,pr2) (cdr ,pr2)))
    (≡ Γ τ e1 pr2)))

(defrel (≡-add1 Γ τ e1 e2)
  (fresh (n1 n2)
    (== e1 `(add1 ,n1))
    (== e2 `(add1 ,n2))
    (== τ 'Nat)
    (≡ Γ 'Nat n1 n2)))

(defrel (≡-ind-Nat Γ τ e1 e2)
  (fresh (t1 m1 b1 s1 t2 m2 b2 s2 τb vars k τ1 τ2 ρ)
    (== e1 `(ind-Nat ,t1 ,m1 ,b1 ,s1))
    (== e2 `(ind-Nat ,t2 ,m2 ,b2 ,s2))
    (normalizo Γ 'UNIVERSE `(,m1 ,t1) τ)
    (≡ Γ 'Nat t1 t2)
    (≡ Γ '(Π ([_ Nat]) U) m1 m2)
    (normalizo Γ 'UNIVERSE `(,m1 zero) τb)
    (≡ Γ τb b1 b2)
    (just-names Γ vars)
    (freshen 'k vars k)
    (extend-ρ Γ k `(NEU NAT (VAR ,k)) ρ)
    (normalizo ρ 'UNIVERSE `(,m1 ,k) τ1)
    (normalizo ρ 'UNIVERSE `(,m1 (add1 ,k)) τ2)
    (≡ Γ `(Π ([,k Nat]) (Π ([_ ,τ1]) ,τ2)) s1 s2)))

(defrel (≡-ind-Nat-ι1 Γ τ e1 e2)
  (fresh (m b s vars k τ1 τ2 ρ)
    (== e1 `(ind-Nat zero ,m ,b ,s))
    (normalizo Γ 'UNIVERSE `(,m zero) τ)
    (≡ Γ '(Π ([_ Nat]) U) m m)
    (≡ Γ τ b e2)
    (just-names Γ vars)
    (freshen 'k vars k)
    (extend-ρ Γ k `(NEU NAT (VAR ,k)) ρ)
    (normalizo ρ 'UNIVERSE `(,m ,k) τ1)
    (normalizo ρ 'UNIVERSE `(,m (add1 ,k)) τ2)
    (≡ Γ '(Π ([,k Nat]) (Π ([_ ,τ1]) ,τ2)) s s)))

(defrel (≡-ind-Nat-ι2 Γ τ e1 e2)
  (fresh (n1 m1 b1 s1 n2 m2 b2 s2 vars k τb τ1 τ2 ρ)
    (== e1 `(ind-Nat (add1 ,n1) ,m1 ,b1 ,s1))
    (== e2 `((,s2 ,n2) (ind-Nat ,n2 ,m2 ,b2 ,s2)))
    (normalizo Γ 'UNIVERSE `(,m1 (add1 ,n1)) τ)
    (normalizo Γ 'UNIVERSE `(,m1 zero) τb)
    (≡ Γ '(Π ([_ Nat]) U) m1 m2)
    (≡ Γ τb b1 b2)
    (just-names Γ vars)
    (freshen 'k vars k)
    (extend-ρ Γ k `(NEU NAT (VAR ,k)) ρ)
    (normalizo ρ 'UNVIERSE `(,m1 ,k) τ1)
    (normalizo ρ 'UNIVERSE `(,m1 (add1 ,k)) τ2)
    (≡ Γ `(Π ([,k Nat]) (Π ([_ ,τ1]) ,τ2)) s1 s2)))

(defrel (≡-λ Γ τ e1 e2)
  (fresh (x r1 y r2 z Arg Argᵥ R R^ Γ^ r2^)
    (== e1 `(λ (,x) ,r1))
    (== e2 `(λ (,y) ,r2))
    (symbolo x)
    (symbolo y)
    (== τ `(Π ([,z ,Arg]) ,R))
    (valofo Γ Arg Argᵥ)
    (extend-Γ Γ x Argᵥ Γ^)
    (substo x y r2 r2^)
    (substo x z R R^)
    (≡ Γ^ R^ r1 r2^)))

(defrel (≡-app Γ τ e1 e2)
  (fresh (f1 arg1 f2 arg2 x A R)
    (== e1 `(,f1 ,arg1))
    (== e2 `(,f2 ,arg2))
    (≡ Γ A arg1 arg2)
    (substo arg1 x R τ)
    (≡ Γ `(Π ([,x ,A]) ,R) f1 f2)))

(defrel (≡-Π-β Γ τ e1 e2)
  (fresh (x r1 arg1 arg2 arg2-v r2 r2^ z y Arg R Γ^)
    (== e1 `((λ (,x) ,r1) ,arg1))
    (≡ Γ Arg arg1 arg2)
    (symbolo y)
    (substo arg2 y r2 e2)
    (substo x y r2 r2^)
    (valofo Γ arg2 arg2-v)
    (extend-Γ Γ x arg2-v Γ^)
    (≡ Γ^ R r1 r2^)
    (symbolo z)
    (substo arg2 z R τ)))

(defrel (≡-Π-η Γ τ e1 e2)
  (fresh (x f2 vars y Arg R)
    (symbolo x)
    (== e2 `(λ (,x) (,f2 ,x)))
    (non-reserved-Pie-fn f2)
    (== τ `(Π ([,y ,Arg]) ,R))
    (≡ Γ τ e1 f2)))

(defrel (≡-= Γ τ e1 e2)
  (fresh (X1 from1 to1 X2 from2 to2)
    (== e1 `(= ,X1 ,from1 ,to1))
    (== e2 `(= ,X2 ,from2 ,to2))
    (≡ Γ 'U X1 X2)
    (≡ Γ X1 from1 from2)
    (≡ Γ X1 to1 to2)))

(defrel (≡-same Γ τ e1 e2)
  (fresh (from to X f t)
    (== e1 `(same ,from))
    (== e2 `(same ,to))
    (== τ `(= ,X ,f ,t))
    (≡ Γ X from f)
    (≡ Γ X from t)
    (≡ Γ X from to)))

(defrel (≡-ind-= Γ τ e1 e2)
  (fresh (t1 m1 b1 t2 m2 b2 X from to vars x τb)
    (== e1 `(ind-= ,t1 ,m1 ,b1))
    (== e2 `(ind-= ,t2 ,m2 ,b2))
    (≡ Γ `(= ,X ,from ,to) t1 t2)
    (normalizo Γ 'UNIVERSE `((,m1 ,to) ,t1) τ)
    (just-names Γ vars)
    (freshen 'x vars x)
    (≡ Γ `(Π ([,x ,X]) (Π ([_ (= ,X ,from ,x)]) U)) m1 m2)
    (normalizo Γ 'UNIVERSE `((,m1 ,from) (same ,from)) τb)
    (≡ Γ τb b1 b2)))

(defrel (≡-ind-=-ι Γ τ e1 e2)
  (fresh (expr m b1 X vars x)
    (== e1 `(ind-= (same ,expr) ,m ,b1))
    (≡ Γ X expr expr)
    (normalizo Γ 'UNIVERSE `((,m ,expr) (same ,expr)) τ)
    (just-names Γ vars)
    (freshen 'x vars x)
    (≡ Γ `(Π ([,x ,X]) (Π ([_ (= ,X ,expr ,x)]) U)) m m)
    (≡ Γ τ b1 e2)))

;; Relevance functions
(define ≡-rules
  '(var the Trivial Triv-η Atom quote Σ cons car Σ-η1 cdr Σ-η
        Nat zero add1 ind-Nat ind-Nat-ι1 ind-Nat-ι2
        Π λ app Π-β Π-η = same ind-= ind-=-ι))
(define elim-rules
  '(var app car cdr Σ-η1 Σ-η2
        ind-Nat ind-Nat-ι1 ind-Nat-ι2 ind-= ind-=-ι the))

(define ignores-e1 '(sole Σ-η Π-η))
(define ignores-e2 '(the Σ-η1 Σ-η2 ind-Nat-ι1 Π-β))

(define (get-rules₁ e)
  (append
   (match e
     [(? simple?) `(,e)]
     [(? symbol?) '(var)]
     [`(the . ,d) '(the)]
     [`(quote ,s) '(quote)]
     [`(add1 ,n) '(add1)]
     [`(Σ . ,d) '(Σ)]
     [`(cons a d) '(cons)]
     [`(car ,pr) '(car Σ-η1)]
     [`(cdr ,pr) '(cdr Σ-η2)]
     [`(ind-Nat . ,d) '(ind-Nat ind-Nat-ι1 ind-Nat-ι2)]
     [`(Π . ,d) '(Π)]
     [`(λ . ,d) '(λ)]
     [`(= . ,d) '(=)]
     [`(same ,v) '(same)]
     [`(ind-= . ,d) '(ind-= ind-=-ι)]
     [`(,rator ,rand) '(app Π-β)]
     [else '()])
   ignores-e1))

(define (get-rules₂ e₂)
  (append
   (match e₂
     [(? simple?) `(,e₂)]
     [(? symbol?) '(var)]
     [`(the . ,d) '(the)]
     [`(quote ,s) '(quote)]
     [`(add1 ,n) '(add1)]
     [`(Σ ((,x ,A)) ,D) '(Σ)]
     [`(Π ((,x ,A)) ,R) '(Π)]
     [`(cons ,a ,d) '(cons Σ-η)]
     [`(car ,pr) '(car)]
     [`(cdr ,pr) '(cdr)]
     [`(ind-Nat . ,d) '(ind-Nat)]
     [`(Π . ,d) '(Π)]
     [`(λ . ,d) '(λ Π-η)]
     [`(= . ,d) '(=)]
     [`(same . ,d) '(same)]
     [`(ind-= . ,d) '(ind-=)]
     [`(,rator ,rand) '(app ind-Nat-ι2)]
     [else '()])
   ignores-e2))

(define (get-rules-for-type τ)
  (match τ
    [(? simple?) (get-constructors τ)]
    [(? symbol?) (get-constructors τ)]
    [(? (exp-memv? '(Σ Π =)))
     (get-constructors (car τ))]
    [(? var?) ≡-rules]
    [else '()]))

(define (≡-table/τ τ)
  (append (get-rules-for-type τ) elim-rules))

(define (lookup-e1 e)
  (match e
    [(? simple?) `(,e)]
    [(? symbol?) '(var)]
    [(? (exp-memv? non-symbol-exprs))
     (get-rules₁ (car e))]
    [`(,rator ,rand) (get-rules₁ 'app)]))

(define (lookup-e2 e)
  (match e
    [(? simple?) `(,e)]
    [(? symbol?) '(var)]
    [(? (exp-memv? non-symbol-exprs))
     (get-rules₂ (car e))]
    [`(,rator ,rand) (get-rules₂ 'app)]))

                   
(define (≡-table/e e)
  (let ([e1 (car e)]
        [e2 (cdr e)])
    (cond
      [(var? e1) (if (var? e2) '(use-out) (lookup-e2 e2))]
      [(var? e2) (lookup-e1 e1)]
      [else (intersection (get-rules₁ e1) (get-rules₂ e2))])))

(defrel (≡ Γ τ e1 e2)
  (condp
    ((`(,e1 . ,e2) ≡-table/e in-mode)
     (τ ≡-table/τ))
    [var (≡-var Γ τ e1 e2)] ;; Hypothesis-Same
    [the (≡-the Γ τ e1 e2)] ;; The
    [Trivial (≡-symbol 'Trivial 'U e1 e2 τ)] ;; USame-Trivial
    [sole (≡-sole Γ τ e1 e2)] ;; TrivSame-η
    [Atom (≡-symbol 'Atom 'U e1 e2 τ)] ;; USame-Atom
    [quote (≡-quote τ e1 e2)] ;; AtomSame-tick
    [Σ (≡-dep-binder 'Σ Γ τ e1 e2)] ;; USame-Σ
    [cons (≡-cons Γ τ e1 e2)] ;; ΣSame-cons
    [car (≡-car Γ τ e1 e2)] ;; ΣSame-car
    [Σ-η1 (≡–Σ-η1 Γ τ e1 e2)] ;; ΣSame-η1
    [cdr (≡-cdr Γ τ e1 e2)] ;; ΣSame-cdr
    [Σ-η2 (≡–Σ-η2 Γ τ e1 e2)] ;; ΣSame-η2
    [Σ-η (≡-Σ-η Γ τ e1 e2)] ;; ΣSame-η
    [Nat (≡-symbol 'Nat 'U e1 e2 τ)] ;; USame-Nat
    [zero (≡-symbol 'zero 'Nat e1 e2 τ)] ;; NatSame-zero
    [add1 (≡-add1 Γ τ e1 e2)] ;; NatSame-add1
    [ind-Nat (≡-ind-Nat Γ τ e1 e2)] ;; NatSame-ind-Nat
    [ind-Nat-ι1 (≡-ind-Nat-ι1 Γ τ e1 e2)] ;; NatSame-in-Nι1
    [ind-Nat-ι2 (≡-ind-Nat-ι2 Γ τ e1 e2)] ;; NatSame-in-Nι2
    [Π (≡-dep-binder 'Π Γ τ e1 e2)] ;; USame-Π
    [λ (≡-λ Γ τ e1 e2)] ;; FunSame-λ
    [app (≡-app Γ τ e1 e2)] ;; FunSame-apply
    [Π-β (≡-Π-β Γ τ e1 e2)] ;; FunSame-β
    [Π-η (≡-Π-η Γ τ e1 e2)] ;; FunSame-η
    [= (≡-= Γ τ e1 e2)] ;; USame-=
    [same (≡-same Γ τ e1 e2)] ;; EQSame-same
    [ind-= (≡-ind-= Γ τ e1 e2)] ;; EqSame-ind-=
    [ind-=-ι (≡-ind-=-ι Γ τ e1 e2)]))
