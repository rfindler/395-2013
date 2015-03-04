#lang racket/base
(require "../fib/fib_iter_gen.rkt"
         plot)

(printf "fib_iter appears to be worse than n * (log(n))^2\n")
(plot 
 (list
  (lines
   #:color "red"
   (for/list ([i (in-range 200)])
     (define-values (ans time) (fib_iter i))
     (vector i time)))
  (lines
   #:color "blue"
   (for/list ([i (in-range 1 200)])
     (vector i (* i (expt (log i) 2)))))))
