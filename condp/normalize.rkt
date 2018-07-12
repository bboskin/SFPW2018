#lang racket

(require "mk.rkt"
         "helpers.rkt")

(provide valofo
         valof-closuro
         normalizo
         read-backo
         read-back-typo)

(defrel (normalizo Γ τ exp o)
  (fresh (v)
    (valofo Γ exp v)
    (read-backo Γ τ v o)))

;; Helpers for valofo

(defrel (assign-simple tₑ tᵥ exp v)
  (== exp tₑ)
  (== v tᵥ))

(defrel (valof-the ρ exp v)
  (fresh (τ e e-v t-v)
    (== exp `(the ,τ ,e))
    (== v `(THE ,t-v ,e-v))
    (valofo ρ e e-v)
    (valofo ρ τ t-v)))

(defrel (valof-neutral-var ρ exp v)
  (fresh (T)
    (== v `(NEU ,T (VAR ,exp)))
    (apply-Γ ρ exp T)))

(defrel (valof-quote ρ exp v)
  (fresh (atom)
    (== exp `(quote ,atom))
    (== v `(ATOM ,atom))))

(defrel (valof-Π ρ exp v)
  (fresh (x A D Ao)
    (== exp `(Π ([,x ,A]) ,D))
    (== v `(PI ,x ,Ao (CLOS ,ρ ,x ,D)))
    (valofo ρ A Ao)))

(defrel (valof-λ ρ exp v)
  (fresh (x b)
    (== exp `(λ (,x) ,b))
    (symbolo x)
    (== v `(LAM ,x (CLOS ,ρ ,x ,b)))))

(defrel (valof-app ρ exp v)
  (fresh (rator rand rato rando)
    (== exp `(,rator ,rand))
    (valofo ρ rator rato)           
    (valofo ρ rand rando)
    (do-appo rato rando v)))

(defrel (valof-closuro clo v ans)
  (fresh (ρ x e ρ^)
    (== clo `(CLOS ,ρ ,x ,e))           
    (extend-ρ ρ x v ρ^)
    (valofo ρ^ e ans)))

(defrel (do-appo f v o)
  (conde
   [(fresh (x c)
      (== f `(LAM ,x ,c))
      (valof-closuro c v o))]
   [(fresh (x A c ne T)
           (== f `(NEU (PI ,x ,A ,c) ,ne))
           (== o `(NEU ,T (N-APP (NEU (PI ,x ,A ,c) ,ne) ,v)))
           (valof-closuro c v T))]))

;;;;;;;;;;;;;;;;

(defrel (valof-Σ ρ exp v)
  (fresh (x A D Ao)
    (== exp `(Σ ([,x ,A]) ,D))
    (== v `(SIGMA ,x ,Ao (CLOS ,ρ ,x ,D)))
    (valofo ρ A Ao)))

(defrel (valof-cons ρ exp v)
  (fresh (a d a^ d^)
    (== exp `(cons ,a ,d))
    (== v `(CONS ,a^ ,d^))
    (valofo ρ a a^)
    (valofo ρ d d^)))

(defrel (valof-car ρ exp v)
  (fresh (pr pr^)
    (== exp `(car ,pr))
    (do-caro pr^ v)
    (valofo ρ pr pr^)))

(defrel (do-caro pr v)
  (conde
   [(fresh (a d)
           (== pr `(CONS ,a ,d))
           (== v a))]
   [(fresh (x A D ne)
           (== pr `(NEU (SIGMA ,x ,A ,D) ,ne))
           (== v `(NEU ,A (CAR (NEU (SIGMA ,x ,A ,D) ,ne)))))]))

(defrel (valof-cdr ρ exp v)
  (fresh (pr pr^)
    (== exp `(cdr ,pr))
    (valofo ρ pr pr^)
    (do-cdro pr^ v)))


(defrel (do-cdro pr v)
  (conde
   [(fresh (a d)
           (== pr `(CONS ,a ,d))
           (== v d))]
   [(fresh (x A D D^ ne a)
           (== pr `(NEU (SIGMA ,x ,A ,D) ,ne))           
           (do-caro pr a)           
           (valof-closuro D a D^)
           (== v `(NEU ,D^ (CDR (NEU (SIGMA ,x ,A ,D) ,ne)))))]))

;;;;;;;;;;;;;;

(defrel (valof-add1 ρ exp v)
  (fresh (n nV)
    (== exp `(add1 ,n))
    (== v `(ADD1 ,nV))
    (valofo ρ n nV)))

(defrel (valof-ind-Nat ρ exp v)
  (fresh (t m τ ba s tV mV bV^ bV sV T)
    (== exp `(ind-Nat ,t ,m (the ,τ ,ba) ,s))
    (== bV `(THE ,T ,bV^))
    (valofo ρ t tV)
    (valofo ρ m mV)
    (valofo ρ ba bV^)
    (valofo ρ τ T)
    (valofo ρ s sV)
    (do-ind-Nat tV mV bV sV v)))

(defrel (do-ind-Nat t m b s o)
  (conde
   [(fresh (τ) (== t 'ZERO) (== b `(THE ,τ ,o)))]
   [(fresh (n res f^) (== t `(ADD1 ,n))
           (do-ind-Nat n m b s res)
           (do-appo s n f^)
           (do-appo f^ res o))]
   [(fresh (ne τ bas)
           (== t `(NEU NAT ,ne))
           (== o `(NEU ,τ (IND-NAT ,t ,m ,b ,s)))
           (do-appo m t τ))]))

;;;;;;;;;;;;;;;;;

(defrel (valof-= ρ exp v)
  (fresh (X from to Xv fromv tov)
    (== exp `(= ,X ,from ,to))
    (== v `(EQUAL ,Xv ,fromv ,tov))
    (valofo ρ X Xv)
    (valofo ρ from fromv)
    (valofo ρ to tov)))

(defrel (valof-same ρ exp v)
  (fresh (e eᵥ)
    (== exp `(same ,e))
    (== v `(SAME ,eᵥ))
    (valofo ρ e eᵥ)))

(defrel (valof-ind-= ρ exp v)
  (fresh (t m b tV mV bV)
    (== exp `(ind-= ,t ,m ,b))
    (valofo ρ t tV)
    (valofo ρ m mV)
    (valofo ρ b bV)
    (do-ind-= ρ tV mV bV v)))

(defrel (do-ind-= ρ t m b o)
  (conde
   [(fresh (v f1 τ) (== t  `(SAME ,v))
           (== o b))]
   [(fresh (A from to ne f1 τ vars Tvar p Ao Fo To f2 τb)
      (== t `(NEU (EQUAL ,A ,from ,to) ,ne))
      (== o `(NEU ,τ
                  (IND-=
                   (NEU (EQUAL ,A ,from ,to) ,ne)
                   (THE (PI ,Tvar ,A (CLOS ,ρ ,Tvar (Π ([,p (= ,Ao ,Fo ,To)]) U))) ,m)
                   (THE ,τb ,b))))(do-appo m to f1)
      (just-names ρ vars)
      (freshen 'to vars Tvar)
      (freshen 'p vars p)
      (do-appo f1 t τ)
      (read-back-typo ρ A Ao)
      (read-backo ρ A from Fo)
      (read-backo ρ A to To)
      (do-appo m from f2)
      (do-appo f2 `(SAME ,from) τb))]))

;; relevance functions for valofo

(define (valofo-in exp)
  (match exp
    [(? simple?) (list exp)]
    [(? symbol?) '(var)]
    [(? (exp-memv? non-symbol-exprs)) (list (car exp))]
    [`(,rat ,ran) '(app)]
    [(? var?) '(use-out)]))

(define (valofo-out v)
  (match v
    [`(NEU ,t ,e) '(var ind-Nat ind-= car cdr app)]
    [else all-exprs]))

(defrel (valofo ρ exp v)
  (condp
    ((exp valofo-in in-mode)
     (v valofo-out))
    ; The expressions
    [the (valof-the ρ exp v)]
    [zero (assign-simple 'zero 'ZERO exp v)]
    [Atom (assign-simple 'Atom 'ATOM exp v)]
    [Nat (assign-simple 'Nat 'NAT exp v)]
    [U (assign-simple 'U 'UNIVERSE exp v)]
    [Trivial (assign-simple 'Trivial 'TRIVIAL exp v)]
    [sole (assign-simple 'sole 'SOLE exp v)]
    [var (apply-ρ ρ exp v)]
    [var (valof-neutral-var ρ exp v)]
    [quote (valof-quote ρ exp v)]
    [add1 (valof-add1 ρ exp v)]
    [ind-Nat (valof-ind-Nat ρ exp v)]
    [Σ (valof-Σ ρ exp v)]
    [cons (valof-cons ρ exp v)]
    [car (valof-car ρ exp v)]
    [cdr (valof-cdr ρ exp v)]
    [= (valof-= ρ exp v)]
    [same (valof-same ρ exp v)]
    [ind-= (valof-ind-= ρ exp v)]
    [Π (valof-Π ρ exp v)]
    [λ (valof-λ ρ exp v)]
    [app (valof-app ρ exp v)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrel (not-LAM e)
  (conde
    [(symbolo e)]
    [(fresh (a d)
       (== e `(,a . ,d))
       (=/= a 'LAM))]))

;; helpers for read-backo
(defrel (read-back-λ Γ τ v norm)
  (fresh (x A c z x^ vars Γ^ B b inner Av)
    (== τ `(PI ,x ,A ,c))
    (== norm `(λ (,x^) ,inner))
    (conde
      [(fresh (y λc) (== v `(LAM ,y ,λc))
              (== z y))]
      [(not-LAM v) (== z x)])
    (symbolo z)
    (just-names Γ vars)
    (freshen z vars x^)
    (extend-Γ Γ x^ A Γ^)
    (valof-closuro c `(NEU ,A (VAR ,x^)) B)
    (do-appo v `(NEU ,A (VAR ,x^)) b)
    (read-backo Γ^ B b inner)))

(defrel (read-back-same Γ τ v norm)
  (fresh (X from to val vo)
    (== τ `(EQUAL ,X ,from ,to))
    (== v `(SAME ,val))
    (== norm `(same ,vo))
    (read-backo Γ X val vo)))

(defrel (read-back-cons Γ τ v norm)
  (fresh (x A c a a^ d d^ D)
    (== τ `(SIGMA ,x ,A ,c))
    (== norm `(cons ,a^ ,d^))
    (do-caro v a)
    (read-backo Γ A a a^)
    (valof-closuro c a D)
    (do-cdro v d)
    (read-backo Γ D d d^)))

(defrel (read-back-Nat Γ τ v norm)
  (== τ 'NAT)
  (conde
    [(== v 'ZERO) (== norm 'zero)]
    [(fresh (n nF)
       (== v `(ADD1 ,n))
       (== norm `(add1 ,nF))
       (read-backo Γ 'NAT n nF))]))

(defrel (read-back-quote Γ τ v norm)
  (fresh (at)
    (== τ 'ATOM)
    (== v `(ATOM ,at))
    (symbolo at)
    (== norm `(quote ,at))))

(defrel (read-back-the Γ τ v norm)
  (fresh (t e tₒ eₒ)
    (== v `(THE ,t ,e))
    (== norm `(the ,tₒ ,eₒ))
    (read-back-typo Γ t tₒ)
    (read-backo Γ τ e eₒ)))

(defrel (go-to-neutral Γ τ v norm)
  (fresh (τ ne)
    (== v `(NEU ,τ ,ne))
    (read-back-neutral τ Γ ne norm)))

(defrel (go-to-type Γ τ v norm)
  (== τ 'UNIVERSE)
  (read-back-typo Γ v norm))


;; relevance function for read-backo

(define (in-type? e τ)
  (let ([cs (get-constructors τ)])
    (or (memv e cs)
        (and (pair? e)
             (member (car e) cs)))))

(define (read-back-v v)
  (match v
    [`(THE ,t ,e) '(the)]
    [`(NEU ,t ,e) '(neutral)]
    [(? var?) '(use-out)]
    [else '()]))

(define (read-back-τ t)
  (match t
    ['UNIVERSE '(U)]
    ['TRIVIAL '(Trivial)]
    ['NAT '(Nat)]
    ['ATOM '(Atom)]
    [`(SIGMA . ,info) '(Σ)]
    [`(EQUAL . ,info) '(=)]
    [`(PI . ,info) '(Π)]
    [(? var?) '(use-out)]
    [else '(the neutral)]))

(define (read-back-norm e)
  (let loop ([t '(Nat Trivial Atom Σ Π = U)])
    (cond
      [(null? t) '()]
      [(in-type? e (car t)) `(,(car t) neutral the)]
      [else (loop (cdr t))])))

(defrel (read-backo Γ τ v norm)
  (condp
    ((v read-back-v in-mode)
     (τ read-back-τ in-mode)
     (norm read-back-norm))
    ;; Types
    [U (go-to-type Γ τ v norm)]
    ;; The
    [the (read-back-the Γ τ v norm)]
    [neutral (go-to-neutral Γ τ v norm)]
    [Trivial (== τ 'TRIVIAL) (== v 'SOLE) (== norm 'sole)]
    [Atom (read-back-quote Γ τ v norm)]
    [Nat (read-back-Nat Γ τ v norm)]
    [Σ (read-back-cons Γ τ v norm)]
    [= (read-back-same Γ τ v norm)]
    [Π (read-back-λ Γ τ v norm)]))

;;;;;;;;;;;;;;;;;;;;;;;;

;; helpers for read-back-typo

(defrel (read-back-dep-binder tag₁ tag₂ Γ v norm)
  (fresh (x A c vars x^ A^ Dv D^ Γ^)
    (== v `(,tag₁ ,x ,A ,c))
    (== norm `(,tag₂ ([,x^ ,A^]) ,D^))
    (just-names Γ vars)
    (freshen x vars x^)
    (read-back-typo Γ A A^)
    (extend-Γ Γ x^ A Γ^)
    (valof-closuro c `(NEU ,A (VAR ,x^)) Dv)
    (read-back-typo Γ^ Dv D^)))

(defrel (read-back-= Γ v norm)
  (fresh (X to from Xo too fromo) 
    (== v `(EQUAL ,X ,from ,to))
    (== norm `(= ,Xo ,fromo ,too))
    (read-back-typo Γ X Xo)
    (read-backo Γ X from fromo)
    (read-backo Γ X to too)))

(defrel (read-back-type-neutral Γ v norm)
  (fresh (ne)
    (== v `(NEU UNIVERSE ,ne))
    (read-back-neutral 'UNIVERSE Γ ne norm)))

;; relevance functions for read-back-typo

(define (RBT-v v)
  (match v
    [(? symbol?) `(,v)]
    [`(PI . ,info) '(Π)]
    [`(EQUAL . ,info) '(=)]
    [`(SIGMA . ,info) '(Σ)]
    [`(NEU . ,info) '(neutral)]
    [(? var?) '(use-out)]
    [else '()]))

(define (RBT-n e)
  (match e
    ['Atom '(ATOM)]
    ['Trivial '(TRIVIAL)]
    ['Nat '(NAT)]
    ['U '(UNIVERSE)]
    [`(Π . ,info) '(Π)]
    [`(= . ,info) '(=)]
    [`(Σ . ,info) '(Σ)]
    [(? var?) '(ATOM NAT UNIVERSE TRIVIAL Σ Π = neutral)]
    [else '(neutral)]))

(defrel (read-back-typo Γ v norm)
  (condp
    ((v RBT-v in-mode)
     (norm RBT-n))
    [ATOM (assign-simple 'ATOM 'Atom v norm)]
    [NAT (assign-simple 'NAT 'Nat v norm)]
    [UNIVERSE (assign-simple 'UNIVERSE 'U v norm)]
    [TRIVIAL (assign-simple 'TRIVIAL 'Trivial v norm)]
    [Σ (read-back-dep-binder 'SIGMA 'Σ Γ v norm)]
    [= (read-back-= Γ v norm)]
    [Π (read-back-dep-binder 'PI 'Π Γ v norm)]
    [neutral (read-back-type-neutral Γ v norm)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; helpers for read-back-neutral

(defrel (RBN-var ne norm)
  (fresh (s)
    (== ne `(VAR ,s))
    (== norm s)))

(defrel (RBN-car τ Γ ne norm)
  (fresh (pr τ-pr pr^)
    (== ne `(CAR (NEU ,τ-pr ,pr)))
    (== norm `(car ,pr^))
    (read-back-neutral τ-pr Γ pr pr^)))

(defrel (RBN-cdr τ Γ ne norm)
  (fresh (τ-pr pr pr^)
    (== ne `(CDR (NEU ,τ-pr ,pr)))
    (== norm `(cdr ,pr^))
    (read-back-neutral τ-pr Γ pr pr^)))

(defrel (RBN-app τ Γ ne norm)
  (fresh (rat ran rato rano x A c T)
    (== ne `(N-APP (NEU (PI ,x ,A ,c) ,rat) ,ran))
    (== norm `(the ,T (,rato ,rano)))
    (read-back-neutral `(PI ,x ,A ,c) Γ rat rato)
    (read-backo Γ A ran rano)
    (read-back-typo Γ τ T)))

(defrel (RBN-ind-Nat τ Γ ne norm)
  (fresh (t m b s to mo bo so T τB TB T1 T2 vars n-1 res Γ^ k-1)
    (== ne `(IND-NAT (NEU NAT ,t) ,m (THE ,τB ,b) ,s))
    (== norm `(ind-Nat ,to ,mo (the ,TB ,bo) ,so))
    (read-back-neutral 'NAT Γ t to)
    (just-names Γ vars)
    (freshen 'k-1 vars k-1)
    (read-backo Γ `(PI ,k-1 NAT (CLOS ,Γ ,k-1 U)) m mo)
    (read-backo Γ τB b bo)
    (read-back-typo Γ τ T)
    (read-back-typo Γ τB TB)
    (freshen 'n-1 vars n-1)
    (freshen 'res vars res)
    (extend-Γ Γ n-1 'NAT Γ^)
    (read-backo Γ `(PI ,n-1 NAT (CLOS ,Γ ,n-1 (Π ([,res (,mo ,n-1)])
                                                (,mo (add1 ,n-1))))) s so)))

(defrel (RBN-ind-= τ Γ ne norm)
  (fresh (A from to ne1 τm m τb b neo mo bo)
    (== ne `(IND-= (NEU (EQUAL ,A ,from ,to) ,ne1)
                   (THE ,τm ,m)
                   (THE ,τb ,b)))
    (== norm `(ind-= ,neo ,mo ,bo))
    (read-back-neutral `(EQUAL ,A ,from ,to) Γ ne1 neo)
    (read-backo Γ τm m mo)
    (read-backo Γ τb b bo)))

;; relevance function for read-back-neutral

(define all-RBN
  '(VAR CAR CDR N-APP IND-NAT IND-=))

(define (RBN-ne v)
  (match v
    [(? (exp-memv? all-RBN)) `(,(car v))]
    [(? var?) all-RBN]
    [else '()]))

(defrel (read-back-neutral τ Γ ne norm)
  (condp
    ((ne RBN-ne in-mode))
    [VAR (RBN-var ne norm)]
    [CAR (RBN-car τ Γ ne norm)]
    [CDR (RBN-cdr τ Γ ne norm)]
    [N-APP (RBN-app τ Γ ne norm)]
    [IND-NAT (RBN-ind-Nat τ Γ ne norm)]
    [IND-= (RBN-ind-= τ Γ ne norm)]))
