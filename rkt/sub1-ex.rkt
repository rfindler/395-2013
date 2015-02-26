#lang racket/base

(require (prefix-in : "../sub1/sub1_gen.rkt") plot)

(define (time-sub1-loop n)
  (let loop ([n n]
             [time-total 0])
    (cond
      [(zero? n) time-total]
      [else
       (define-values (ans time) (:sub1 n))
       ;; just make sure I didn't get the results in the wrong order
       (unless (= ans (- n 1)) (error 'ack))
       (loop (- n 1)
             (+ time-total time))])))

(plot
 #:x-label "counting down from this number"
 #:y-label "abstract number of steps"
 (lines
  (for/list ([i (in-range 10000)])
    (define the-time (time-sub1-loop i))
    (define lb (- (* i 17) 16))
    (define ub (* i 20))
    (unless (<= lb the-time ub)
      (eprintf "~a: ~a ~a\n" i 
               (- the-time lb)
               (- the-time ub)))
    (vector i the-time))))

