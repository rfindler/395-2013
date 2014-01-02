#lang racket/base
(provide (all-defined-out))

;; a braun tree is either #f or (node any braun-tree bran-tree nat)
(struct node (v l r s) #:transparent)

(define (size n)
  (cond
    [(node? n) (node-s n)]
    [else 0]))

(define (mknode l r #:val [v #f])
  (unless (<= (size r) (size l) (+ (size r) 1))
    (error 'mknode "invariant check failed:\n  (size l) = ~s   l = ~s\n  (size r) = ~s   r = ~s" 
           (size l) l
           (size r) r))
  (node v l r (+ (size l) (size r) 1)))


;; no tests
(module test racket/base)