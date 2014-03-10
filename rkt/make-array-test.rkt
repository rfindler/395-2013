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
