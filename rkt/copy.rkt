#lang racket
(require "braun.rkt")

(provide (all-defined-out))

(define (copy2 n)
  (cond
    [(zero? n) (values (mknode #f #f) #f)]
    [(odd? (- n 1))
     (define-values (s t) (copy2 (/ (- n 2) 2)))
     (values (mknode s s) (mknode s t))]
    [(even? (- n 1))
     (define-values (s t) (copy2 (/ (- n 1) 2)))
     (values (mknode s t) (mknode t t))]))

(define/contract (copy n)
  (->i ([n natural-number/c])
       [result (n) (λ (b) (= (size b) n))])
  (define-values (s t) (copy2 n))
  t)

(module+ test
  (printf "testing braun tree invariants for copy\n")
  (for ([i (in-range 1000)]) (copy i)))