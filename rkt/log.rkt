#lang racket
(provide (all-defined-out))

(define (div2 n) (quotient n 2))

(define (fl_log-slow n)
  (cond
    [(zero? n) 0]
    [else (+ (fl_log (div2 (- n 1))) 1)]))

(define (cl_log-slow n)
  (cond
    [(zero? n) 0]
    [else (+ (cl_log (div2 n)) 1)]))

;; faster versions
(define (cl_log n) (integer-length n))
(define (fl_log n) (sub1 (integer-length (add1 n))))


(module+ test
  (printf "testing fl_log and cl_log\n")
  (unless (equal? (map fl_log '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))
                  (map values '(0 1 1 2 2 2 2 3 3 3 3  3  3  3  3  4)))
    (error 'fl_log "wrong"))
  
  (unless (equal? (map cl_log '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))
                  (map values '(0 1 2 2 3 3 3 3 4 4 4  4  4  4  4  4)))
    (error 'cl_log "wrong"))
  
  (printf "testing against fl_log-slow and cl_log-slow\n")
  (for ([i (in-range 2048)])
    (unless (= (fl_log-slow i) (fl_log i))
      (error 'fl_log "slow doesn't match for ~a"))
    (unless (= (cl_log-slow i) (cl_log i))
      (error 'cl_log "slow doesn't match for ~a"))))
