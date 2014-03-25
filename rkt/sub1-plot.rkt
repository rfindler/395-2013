#lang racket

(require plot
         (prefix-in : "sub1.rkt")
         "sub1_linear.rkt"
         "sub1_div2.rkt"
         "copy_linear_sub1.rkt"
         "diff_sub1.rkt"
         "log.rkt")

(define n 1000)
(define (assert<= fn bound-fn n)
  (let loop
    ([i 0]
     [cur 1])
    (define lower (fn cur))
    (define higher (bound-fn cur))
    (unless (lower . <= . higher)
      (error "should be less but it ain't" cur lower higher))
    (cond [(i . >= . n) 0]
          [else (loop (+ i 1)
                      (+ (random 100)(* 2 cur)))])))

(define (plot-with-bound n mk-points bound-fn)
  (plot
   (list
    (mk-points n)
    (lines #:color 'green
     (for/list ([i (in-range n)])
      (vector i (bound-fn i)))))))

(define (get-time fn x)
  (define-values (_ time) (fn x))
  time)

;;;;;;;; sub1_linear
;; Bounded by linear
;; take/drop
(define (sub1_linear_points n)
  (points
   (for/list ([i (in-range n)])
     (vector i (get-time sub1_linear i)))))
(define (sub1_linear_bound n)
  (10 . + . (30 . * . n)))

(plot-with-bound n sub1_linear_points sub1_linear_bound)

;;;;;;;; sub1_div2
;; Bounded by a log
;; copy2, copy_insert
(define (sub1_div2_points n)
  (points
   (for/list ([i (in-range n)])
     (define-values (ans time) (sub1_div2 i))
     (vector i time))))
(define (sub1_div2_bound n)
  (+ 20 (* 30 (fl_log n))))

(plot-with-bound n sub1_div2_points sub1_div2_bound)
#;(assert<= (curry get-time sub1_div2) sub1_div2_bound 1000)

;;;;;;;; diff
;; Bounded by log
(define (diff_sub1_points n)
  (points
   (append
    (for/list ([i (in-range n)])
     (define-values (ans time) (diff_sub1 i i))
     (vector i time))
    (for/list ([i (in-range n)])
      (define-values (ans time) (diff_sub1 (+ 1 i) i))
      (vector i time)))))
(define (diff_sub1_bound n)
  (+ 3 (* 45 (fl_log n))))
(plot-with-bound n diff_sub1_points diff_sub1_bound)

;; Bounded by linear
(define (copy_linear_sub1_points n)
  (lines
   (for/list ([i (in-range n)])
     (define-values (ans time) (copy_linear_sub1 i))
     (vector i time))))
(define (copy_linear_sub1_bound n)
  (n . * . 40))
(plot-with-bound n copy_linear_sub1_points copy_linear_sub1_bound)
