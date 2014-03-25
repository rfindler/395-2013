#lang racket

(require plot/pict
         (prefix-in : "sub1.rkt")
         "sub1_linear.rkt"
         "sub1_div2.rkt"
         "copy_linear_sub1.rkt"
         "diff_sub1.rkt"
         "log.rkt")

(provide plot-with-bound copy_linear_sub1_points copy_linear_sub1_bound)

(define n 1000)
(define logn 
  ((log n) . / . (log 2)))
(define (assert<=-linear n fn bound-fn)
  (for ([i (in-range n)])
    (define lower (fn i))
    (define higher (bound-fn i))
    (unless (lower . <= . higher)
      (error "should be less but it ain't" i lower higher))))

(define (assert<=-log n fn bound-fn)
  (let loop
    ([i 0]
     [cur 1])
    (define lower (fn cur))
    (define higher (bound-fn cur))
    (unless (lower . <= . higher)
      (error "should be less but it ain't" cur lower higher))
    (unless (i . >= . n)
      (loop (+ i 1)
            (+ (random 100)(* 2 cur))))))

(define (plot-with-bound n mk-points bound-fn)
  (plot-pict
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
  (10 . + . (40 . * . n)))
(module+ main
  (plot-with-bound n sub1_linear_points           sub1_linear_bound))
(module+ test
  (assert<=-linear n (curry get-time sub1_linear) sub1_linear_bound))

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

(module+ main
  (plot-with-bound n sub1_div2_points sub1_div2_bound))
(module+ test
  (assert<=-log logn (curry get-time sub1_div2) sub1_div2_bound))

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
(define (diff_sub1_different n)
  (define-values (_ t) (diff_sub1 (+ n 1) n))
  t)
(define (diff_sub1_same n)
  (define-values (_ t) (diff_sub1 n n))
  t)
(define (diff_sub1_bound n)
  (+ 3 (* 45 (fl_log n))))
(module+ main
  (plot-with-bound n diff_sub1_points diff_sub1_bound))
(module+ test
  (assert<=-log logn diff_sub1_same diff_sub1_bound)
  (assert<=-log logn diff_sub1_different diff_sub1_bound))

;; Bounded by linear
(define (copy_linear_sub1_points n)
  (lines
   (for/list ([i (in-range n)])
     (define-values (ans time) (copy_linear_sub1 i))
     (vector i time))))

(define (copy_linear_sub1_bound n)
  (+ 29 (n . * . 31)))
(module+ main
  (plot-with-bound n copy_linear_sub1_points copy_linear_sub1_bound))
(module+ test
  (assert<=-linear n (curry get-time copy_linear_sub1) copy_linear_sub1_bound))
