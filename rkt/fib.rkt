#lang racket

(require plot
         "log.rkt"
         math/base
         racket/trace)

(define (fib n)
  (cond
    [(= n 0) 0]
    [(= n 1) 1]
    [else (+ (fib (- n 1))
             (fib (- n 2)))]))

#|
  Program Fixpoint rt_copy_fib (n : nat) {measure n}: nat :=
    match n with 
      | 0 => 1
      | (S n') => if (even_odd_dec n)
                  then (S ((rt_copy_fib (div2 n)) + (rt_copy_fib (div2 n'))))
                  else (S (rt_copy_fib (div2 n)))
    end. 
|#

(define (rtcf n)
  (cond
    [(= n 0) 1]
    [(even? n) (+ 1 (rtcf (div2 n)) (rtcf (div2 (sub1 n))))]
    [else (+ 1 (rtcf (div2 n)))]))

#|
 P2MO (2^n - 1) = 1 + P2MO (2^(n-1) - 1)
  (fl_log)
|#

(define (p2sub1 n)
  (cond
    [(zero? n) 1]
    [else (+ 1 (p2sub1 (div2 n)))]))

#|
  P2 2^n = 1 + P2 2^(n-1) + P2MO (2^(n-1) - 1)
|#

(define (p2 n)
  (cond
    [(zero? n) 0]
    [else (+ 1 (p2 (div2 n)) (p2sub1 (div2 (sub1 n))))]))

(define pows (list 8 16 32 64 128 256 512))
(define maxes  (list 12 26 52 106 212 426))

;; maxes (between powers of 2) are at the
;; generalized Jacobsthal numbers:
;; 5*2^n/3 + (-1)^n/3 - 1
;; http://oeis.org/A084170
(define (gj n)
  (+ (* (/ 5 3) (expt 2 n))
     (/ (expt (- 1) n) 3)
     (- 1)))

;; recursive spec for the gjn's
;; a(n)=a(n-1)+2*a(n-2)+2, a(0)=1, a(1)=2.
(define (gj2 n)
  (cond
    [(= n 0) 1]
    [(= n 1) 2]
    [else (+ (gj2 (- n 1))
             (* 2 (gj2 (- n 2)))
             2)]))

(define gjs (for/list ([n (in-range 10)]) (gj n)))
(define (is-gj? n) (member n gjs))

(define (f n)
  (cond
    [(= n 0) 1]
    [(= n 1) 2]
    [else (+ 1
             (f (div2 n))
             (g (div2 n)))]))

(define (g n)
  (cond
    [(= n 0) 1]
    [(= n 1) 1]
    [else (+ 1 (f (div2 n)))]))

#|

even n -> rtcf n <= f n
odd n  -> rtcf n <= g n

|#

(define (make-plot upper-bound)
    (plot
     #:x-label "n"
     (list
      (lines
       #:color 'black
       (for/list ([n (in-range upper-bound)])
         (vector n (rtcf n))))
      (lines 
       #:color 'blue
       (for/list ([n (in-range upper-bound)])
         (vector n (p2sub1 n))))
      (lines 
       #:color 'green
       (for/list ([n (in-range upper-bound)])
         (vector n (p2 n))))
      (lines 
       #:color 'red
       (for/list ([n (in-range upper-bound)])
         (vector n (f n))))
      (lines 
       #:color 'orange
       (for/list ([n (in-range upper-bound)])
         (vector n (g n))))
      (lines 
       #:color 'purple
       (for/list ([n (in-range upper-bound)])
         (vector n (* 6 (fib (cl_log n))))))
      (points
       #:color 'blue
       (for/list ([n (in-range upper-bound)]
                  #:when (power-of-two? n))
         (vector (sub1 n) (rtcf (sub1 n)))))
      (points
       #:color 'green
       (for/list ([n (in-range upper-bound)]
                  #:when (power-of-two? n))
         (vector n (rtcf n))))
      (points
       #:color 'red
       (for/list ([n (in-range upper-bound)]
                  #:when (is-gj? n))
         (vector n (rtcf n)))))))

#;
(trace rtcf
       p2sub1
       p2)