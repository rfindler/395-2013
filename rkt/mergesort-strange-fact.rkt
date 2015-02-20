#lang racket
(require "log.rkt")

(define (strange-fact? n)
  (<= (+ (* (div2 (+ n 4)) (fl_log (+ n 5))) (fl_log (+ n 5)))
      (+ (* (div2 (+ n 4)) (fl_log (+ n 3))) n 5)))

(module+ main
  (let/ec k
    (for ([x (in-naturals)])
      (unless (strange-fact? x)
        (eprintf "failed at ~a\n" x)
        (k (void)))
      (when (zero? (modulo x 10000000))
        (printf "holds up to ~a\n" x)))))
