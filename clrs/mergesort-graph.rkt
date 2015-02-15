#lang racket/base
(require plot)
(plot-new-window? #t)

(define (div2 n)
  (quotient n 2))

(define (split_at_time n)
  (+ (* 2 n) 1))

(define (Mergesortc_Best_Time mbt ibt n)
  (cond
   [(zero? n)
    1]
   [(even? n)
    (define D (Mergesortc_Best_Time mbt ibt (div2 n)))
    (+
     (split_at_time (div2 n))
     D D (mbt (div2 n) (div2 n))
     2)]
   [(odd? n)
    (define D (Mergesortc_Best_Time mbt ibt (sub1 n)))
    (+ D (ibt n) 2)]))

(define (merge_worst_time n m)
  (+ (* 3 (+ n m)) 1))

(define (insert_worst_time n)
  (+ (* 2 n) 1))

(define (log_2 n)
  (/ (log n) (log 2)))

(define (cl_log n)
  (ceiling (log_2 (+ n 1))))

(define (mergesortc_worst_time n)
  (Mergesortc_Best_Time
   merge_worst_time insert_worst_time
   n))

(module+ main
  (plot #:x-min 0
        #:x-max 20000
        #:title "big_oh mwt nlgn"
        (list (function #:label "mergesortc_worst_time"
                        #:color 0
                        (λ (n) (mergesortc_worst_time (floor n))))
              (function #:label "n lg n + 1 [c = 6]"
                        #:color 1
                        (λ (n) (* 6 (+ (* n (cl_log n)) 1)))))))

(define (merge_best_time n m)
  (+ (* 3 (min n m)) 1))
(define (insert_best_time n)
  1)

(define (mergesortc_best_time n)
  (Mergesortc_Best_Time
   merge_best_time insert_best_time
   n))

(module+ main-ok
  (plot #:x-min 0
        #:x-max 2000
        #:title "big_omega mbt nlgn"
        (list (function #:label "mergesortc_best_time"
                        #:color 0
                        (λ (n) (mergesortc_best_time (floor n))))
              (function #:label "n lg n"
                        #:color 1
                        (λ (n) (* n (cl_log n)))))))

(define (clength_time n)
  (+ n 1))

(define (mergesort_best_time n)
  (+ (clength_time n)
     (mergesortc_best_time n)))

(module+ main-ok
  (plot #:x-min 0
        #:x-max 2000
        #:title "big_omega mbt nlgn"
        (list (function #:label "mergesort_best_time"
                        #:color 0
                        (λ (n) (mergesort_best_time (floor n))))
              (function #:label "n lg n"
                        #:color 1
                        (λ (n) (* n (cl_log n)))))))
