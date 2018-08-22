#lang racket
(require "mk.rkt")


;; conde definition of swap-some
(defrel (swap-someᵒ ls o)
  (conde
   ((== '() ls) (== '() o))
   ((fresh (a d res)
      (== `(,a . ,d) ls)
      (== `(,a . ,res) o)
      (swap-someᵒ d res)))
   ((fresh (a d res)
      (== `(,a . ,d) ls)
      (== `(novel . ,res) o)
      (swap-someᵒ d res)))))

;; condp-ized version, with suggestion functions


(define (ls-keys ls)
  (cond
    ((var? ls) '(use-maybe))
    ((null? ls) '(BASE))
    ((pair? ls) '(KEEP SWAP))
    (else '())))

(define (o-keys o)
  (cond
    ((var? o) '(BASE KEEP SWAP))
    ((null? o) '(BASE))
    ((pair? o)
     (if (or (var? (car o))
             (eqv? 'novel (car o)))
         '(KEEP SWAP)
         '(KEEP)))
    (else '())))


(defrel (swap-someᵖ ls o)
  (condp
   (((ls-keys ls))
    ((o-keys o)))
   (BASE (== '() ls) (== '() o))
   (KEEP (fresh (a d res)
           (== `(,a . ,d) ls)
           (== `(,a . ,res) o)
           (swap-someᵖ d res)))
   (SWAP (fresh (a d res)
           (== `(,a . ,d) ls)
           (== `(novel . ,res) o)
           (swap-someᵖ d res)))))

#;
(equal? (run* (q) (swap-someᵒ q `(novel fish)))
        (run* (q) (swap-someᵖ q `(novel fish))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Second version of swap-some, with nested conde's
(defrel (swap-someᵒ₂ ls o)
  (conde
   ((== '() ls) (== '() o))
   ((fresh (a d res)
      (== `(,a . ,d) ls)
      (conde
       ((== `(,a . ,res) o))
       ((== `(novel . ,res) o)))
      (swap-someᵒ₂ d res)))))


;; condp-ized version of second version

(define (ls-keys-outer ls)
  (cond
    ((var? ls) '(use-maybe))
    ((null? ls) '(BASE))
    ((pair? ls) '(REC))
    (else '())))

(define (o-keys-outer o)
  (cond
    ((var? o) '(BASE REC))
    ((null? o) '(BASE))
    ((pair? o) '(REC))
    (else '())))

;;;;;;

(define (ls-keys-inner ls)
  (cond
    ((var? ls) '(use-maybe))
    (else '(KEEP SWAP))))

(define (o-keys-inner o)
  (cond
    ((var? o) '(KEEP SWAP))
    ((pair? o)
     (if (or (var? (car o))
             (eqv? 'novel (car o)))
         '(KEEP SWAP)
         '(KEEP)))
    (else '())))

(defrel (swap-someᵖ₂ ls o)
  (condp
   (((ls-keys-outer ls))
    ((o-keys-outer o)))
   (BASE (== '() ls) (== '() o))
   (REC (fresh (a d res)
          (== `(,a . ,d) ls)
          (condp
           (((ls-keys-inner ls))
            ((o-keys-inner o)))
           (KEEP (== `(,a . ,res) o))
           (SWAP (== `(novel . ,res) o)))
          (swap-someᵖ₂ d res)))))


(equal? (run* (q) (swap-someᵒ₂ q `(novel fish)))
        (run* (q) (swap-someᵖ₂ q `(novel fish))))
