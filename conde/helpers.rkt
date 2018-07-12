#lang racket

(require "mk.rkt")

(provide membero
         not-membero
         removo
         uniono
         intersection
         
         non-reserved-Pie-fn
         reserved-Pie-symbol
         non-reserved-Pie-symbol

         apply-Γ
         apply-ρ
         extend-Γ
         extend-ρ
         extend-env
         
         free-in-Γ
         free-in-ρ
         just-names
         freshen
         fresh-name)

;; simple list ops
(defrel (membero x ls)
  (fresh (a d)
    (== ls `(,a . ,d))
    (conde
      [(== x a)]
      [(=/= x a)
       (membero x d)])))

(defrel (not-membero x ls)
  (conde
    [(== ls '())]
    [(fresh (a d)
       (== ls `(,a . ,d))
       (=/= x a)
       (not-membero x d))]))

(defrel (removo x ls o)
  (conde
    [(== ls '()) (== o '())]
    [(fresh (d)
       (== ls `(,x . ,d))
       (removo x d o))]
    [(fresh (a d o^)
       (=/= x a)
       (== ls `(,a . ,d))
       (removo x d o^)
       (== o `(,a . ,o^)))]))

(defrel (uniono l1 l2 o)
  (conde
    [(== l1 '()) (== o l2)]
    [(fresh (a d o^ rm)
       (== l1 `(,a . ,d))
       (uniono d l2 o^)
       (removo a o^ rm)
       (== o `(,a . ,rm)))]))

(define (intersection e1 e2)
  (cond
    [(null? e1) '()]
    [(memv (car e1) e2)
     (cons (car e1)
           (intersection (cdr e1) e2))]
    [else (intersection (cdr e1) e2)]))

;; predicates about symbols

;; symbols that might be confused with a function of 1 argument
(defrel (non-reserved-Pie-fn s)
  (fresh ()
    (=/= s 'add1)
    (=/= s 'car)
    (=/= s 'cdr)
    (=/= s 'same)))

;; symbols that might be confused with variables
(defrel (reserved-Pie-symbol s)
  (symbolo s)
  (conde
    [(== s 'Atom)]
    [(== s 'zero)]
    [(== s 'Nat)]
    [(== s 'sole)]
    [(== s 'Trivial)]
    [(== s 'U)]))

(defrel (non-reserved-Pie-symbol s)
  (symbolo s)
  (=/= s 'Atom)
  (=/= s 'U)
  (=/= s 'zero)
  (=/= s 'Nat)
  (=/= s 'sole)
  (=/= s 'Trivial))

;;; Environment suite

(defrel (apply-Γ Γ y τ)
  (conde
   [(fresh (Γ^) (== Γ `((free ,y ,τ) . ,Γ^)))]
   [(fresh (Γ^ v) (== Γ `((def ,y ,v ,τ) . ,Γ^)))]
   [(fresh (assoc Γ^)
      (=/= assoc 'free)
      (=/= assoc 'def)
      (== Γ `(,assoc . ,Γ^))
      (apply-Γ Γ^ y τ))]))

(defrel (apply-ρ ρ y v)
  (conde
   [(fresh (ρ^ τ) (== ρ `((def ,y ,v ,τ) . ,ρ^)))]
   [(fresh (ρ^) (== ρ `((val ,y ,v) . ,ρ^)))]
   [(fresh (assoc ρ^)
      (=/= assoc 'val)
      (=/= assoc 'def)
      (== ρ `(,assoc . ,ρ^))
      (apply-ρ ρ^ y v))]))

(defrel (extend-Γ Γ y τ new-Γ)
  (== new-Γ `((free ,y ,τ) . ,Γ)))

(defrel (extend-ρ ρ y v new-ρ)
  (== new-ρ `((val ,y ,v) . ,ρ)))

(defrel (extend-env ρ y v τ new-ρ)
  (== new-ρ `((def ,y ,v ,τ) . ,ρ)))

(defrel (free-in-Γ x Γ)
  (conde
    [(== Γ '())]
    [(fresh (tag y d Γ^)
       (== Γ `((,tag ,y . ,d) . ,Γ^))
       (=/= x y)
       (free-in-Γ x Γ^))]))

(defrel (free-in-ρ x ρ)
  (conde
    [(== ρ '())]
    [(fresh (name τ ρ^)
       (== ρ `((free ,name ,τ) . ,ρ^))
       (free-in-ρ x ρ^))]
    [(fresh (tag name d ρ^)
       (== ρ `((,tag ,name . ,d) . ,ρ^))
       (=/= tag 'free)
       (=/= name x)
       (free-in-ρ x ρ^))]))
         
;;;;;;;;;;;;;;;;;;;;;;
;; Variable freshening

(defrel (just-names Γ names)
  (conde
   [(== Γ '()) (== names '())]
   [(fresh (x v t Γ^ o)
           (conde
            [(== Γ `((def ,x ,v ,t) . ,Γ^))
             (just-names Γ^ o)
             (== names `(,x . ,o))]
            [(== Γ `((free ,x ,t) . ,Γ^))
             (just-names Γ^ o)
             (== names `(,x . ,o))]
            [(== Γ `((val ,x ,v) . ,Γ^))
             (just-names Γ^ o)
             (== names `(,x . ,o))]))]))

(define (add-* x)
  (string->symbol
   (string-append (symbol->string x)
                  "*")))

(defrel (fresh/aux x used name)
  (condu
   [(membero x used) (fresh/aux (add-* x) used name)]
   [(== x name)]))

(defrel (freshen x used name)
  (condu
   [(membero x used) (fresh/aux 'var used name)]
   [(== x name)]))

(defrel (fresh-name o)
  (== o (gensym 'tmp)))

