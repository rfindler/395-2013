#lang racket
(require "../arith/sub1_gen.rkt")
(require plot)
(provide diff-sub/div-plot)

(define (div2 n) (quotient n 2))

(define (diff-sub/div-loop n)
  (define count 0)
  (define (inc) (set! count (add1 count)))
  (define (diff-sub/div-loop/a n acc)
    (inc)
    (cond
      [(zero? n) (+ acc 1)]
      [(even? n)
       (define-values (a1 t1) (sub1 n))
       (define-values (a2 t2) (sub1 a1))
       (diff-sub/div-loop/a (div2 a2) (+ acc t1 t2 1))]
      [(odd? n)
       (define-values (a1 t1) (sub1 n))
       (diff-sub/div-loop/a (div2 a1) (+ acc t1 1))]))
  (values (diff-sub/div-loop/a n 0) count))

(define diff-sub/div-plot
  (plot-pict
   #:width 250
   #:height 250
   #:x-label "Argument to diff"
   #:y-label "Average Number of Abstract Steps"
   (points
    (for/list ([i (in-range 1024)])
      (define-values (time len) (diff-sub/div-loop i))
      (vector i (/ time len))))))

(define (make-bad n)
    (cond
      [(zero? n) 2]
      [else
       (+ (* 4 (make-bad (sub1 n))) 2)]))

(define (t n)
    (define-values (time len) (diff-sub/div-loop (make-bad n)))
    (/ time len))

(define (make-bad2 n)
    (cond
      [(zero? n) 2]
      [else
       (* 2 (+ (make-bad2 (- n 1)) 1))]))



(define (t2 n)
    (define-values (time len) (diff-sub/div-loop (make-bad2 n)))
    (/ time len))
