#lang racket

(require "helpers.rkt"
         "typechecker.rkt"
         "normalize.rkt"
         "mk.rkt")
;; A main program, with defines and check-same
(provide pie)

(defrel (run-pie Γ prog o)
  (conde
    [(fresh (a d)
       (== prog `(,a . ,d))
       (conde
         [(fresh (name τ def τₒ defₒ Γ^ τ-v v)
            (== a `(claim/define ,name ,τ ,def))
            (free-in-Γ name Γ)
            (type Γ τ τₒ)
            (check Γ def τₒ defₒ)
            (valofo Γ τₒ τ-v)
            (valofo Γ defₒ v)
            (extend-env Γ name v τ-v Γ^)
            (run-pie Γ^ d o))]
         [(fresh (τ e1 e2 τₒ e1ₒ e2ₒ)
            (== a `(check-same ,τ ,e1 ,e2))
            (type Γ τ τₒ)
            (check Γ e1 τₒ e1ₒ)
            (check Γ e2 τ e2ₒ)
            (≡ Γ τₒ e1ₒ e2ₒ)
            (run-pie Γ d o))]
         [(fresh (res o^)
            (conde
              [(symbolo a)]
              [(fresh (a1 d1)
                 (== a `(,a1 . ,d1))
                 (=/= a1 'check-same)
                 (=/= a1 'define))])
            (synth Γ a res)
            (== o `(,res . ,o^))
            (run-pie Γ d o^))]))]
    [(== prog '()) (== o '())]))

(defrel (pie p o)
  (run-pie '() p o))
