#lang racket/base

(require "make_array_nlogn1.rkt"
         "make_array_nlogn2.rkt"
         "make_array_linear.rkt")

(define (check-against-naive make-array)
  (printf "testing ~a against make_array_naive\n" (object-name make-array))
  (for ([i (in-range 1000)])
    (define l (build-list i values))
    (define-values (t1 time1) (make_array_naive l))
    (define-values (t2 time2) (make-array l))
    (unless (equal? t1 t2)
      (error 'make-array-test.rkt
             "make_array_naive and ~s trees don't match at size ~a:\n  ~s\n  ~s"
             (object-name make-array)
             i
             t1
             t2))))

(check-against-naive make_array_td)
(check-against-naive make_array_linear)

(require racket/contract)
(define/contract (fbt_rs_3 k len)
  (-> (and/c natural-number/c
             (>=/c 1))
      natural-number/c
      natural-number/c)
  (cond
    [(zero? len) 1]
    [else (+ k (fbt_rs_3 (* 2 k) (n- len k)))]))

(define (n- a b) (max 0 (- a b)))

(printf "testing (fbt_rs_3 k n) <= (+ (* 2 n) k)\n")
(for ([n (in-range 1000)])
  (for ([k (in-range 1 1000)])
    (define ans (fbt_rs_3 k n))
    (define bound (+ (* 2 n) k))
    (unless (<=  ans bound)
      (eprintf "no! n=~a k=~a; ~s vs ~s\n"
               n
               ans bound))))
