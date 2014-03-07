#lang racket
(require "braun.rkt" "log.rkt"
         (prefix-in fp:
                    (combine-in
                     "diff.rkt"
                     "size_log_sq.rkt"
                     (only-in "tmonad.rkt" bt_node bt_mt))))

(module copy racket
  (require "braun.rkt")
  
  (provide (all-defined-out))
  
  (define (copy2 n)
    (cond
      [(zero? n) (values (mknode #f #f) #f)]
      [(odd? (- n 1))
       (define-values (s t) (copy2 (/ (- n 2) 2)))
       (values (mknode s s) (mknode s t))]
      [(even? (- n 1))
       (define-values (s t) (copy2 (/ (- n 1) 2)))
       (values (mknode s t) (mknode t t))]))
  
  (define/contract (copy n)
    (->i ([n natural-number/c])
         [result (n) (λ (b) (= (size b) n))])
    (define-values (s t) (copy2 n))
    t)
  
  (module+ test
    (printf "testing braun tree invariants for copy\n")
    (for ([i (in-range 1000)]) (copy i))))
(require 'copy)

(define (convert t)
  (cond
    [(node? t) (fp:bt_node (node-v t) 
                           (convert (node-l t))
                           (convert (node-r t)))]
    [else fp:bt_mt]))

;; computes the running time of diff
(define/contract (diff-rt b m)
  ;; contract makes sure argument invariant holds
  (->i ([b (or/c node? #f)]
        [m (b) (λ (m) (<= m (size b) (+ m 1)))])
       any)
  (define-values (result time) (fp:diff (convert b) m))
  time)

(define (non-zero? n) (not (= n 0)))

(module+ test
  (printf "testing upper bound of running time of diff\n")
  (for ([n (in-range 10)])
    (for ([m (in-list (list (- n 1) n))])
      (when (positive? m)
        (define bt (copy n))
        (define d (diff-rt bt m))
        (define f (+ (* 13 (fl_log m)) 4))
        (unless (<= d f)
          (eprintf "diff rt wrong: n = ~a m = ~a d = ~a f = ~a\n" n m d f))))))


(define (diff-rt-in-terms-of-m m)
  (cond
    [(zero? m) 4]
    [else (if (even? m)
              (+ 13 (diff-rt-in-terms-of-m (div2 (- m 2))))
              (+ 11 (diff-rt-in-terms-of-m (div2 (- m 1)))))]))

(module+ test
  (printf "testing exact running time of diff\n")
  (for ([n (in-range 1000)])
    (for ([m (in-list (list (- n 1) n))])
      (when (positive? m)
        (define bt (copy n))
        (define d (diff-rt bt m))
        (define f (diff-rt-in-terms-of-m m))
        (unless (= d f)
          (eprintf "diff rt wrong: n = ~a m = ~a delta ~a\n" n m (- d f)))))))

(define (size-rt-in-terms-of-bt-size n)
  (cond
    [(zero? n) 3]
    [else (+ (diff-rt-in-terms-of-m (div2 (- n 1)))
             (size-rt-in-terms-of-bt-size (div2 (- n 1)))
             13)]))

(module+ test
  (printf "testing exact running time of size\n")
  (for ([n (in-range 3000)])
    (define bt (copy n))
    (define d (loglog-size-rt bt))
    (define f (size-rt-in-terms-of-bt-size n))
    (unless (= d f)
      (eprintf "size rt wrong: n = ~a delta ~a\n" n (- d f)))))

;; compute the running time of the loglog-size function
(define (loglog-size-rt b)
  (define-values (result time) (fp:size (convert b)))
  time)

(define (sum-of-logs n)
  (cond
    [(zero? n) 3]
    [(odd? n)  (+ (* 13 (fl_log n)) 17 (sum-of-logs (div2 (- n 1))))]
    [(even? n) (+ (* 13 (cl_log n)) 17 (sum-of-logs (div2 (- n 1))))]))

(module+ test
  (printf "testing sum-of-logs\n")
  (for ([n (in-range 200)])
    (define d (loglog-size-rt (copy n)))
    (define f (sum-of-logs n))
    (unless (<= d f)
      (eprintf "size rt wrong: n = ~a d = ~a f = ~a\n" n d f))))

(define (sum-of-logs-ub n) (+ (* 17 (fl_log n) (fl_log n)) 20))

(module+ test
  (printf "testing upper bound of sum-of-logs\n")
  (let loop ([n 1]
             [i 400])
    (unless (zero? i)
      (define ub (sum-of-logs-ub n))
      (define sl (sum-of-logs n))
      (unless (<= sl ub)
        (eprintf "upper bound wrong: n = ~a ub = ~a sl = ~a δ = ~a\n"
                 n ub sl (- ub sl)))
      (loop (+ n n (random 100)) (- i 1)))))

(module+ slideshow
  (require slideshow plot/pict "pict.rkt")
  
  (define (combine picts)
    (define width 800)
    (define gap 4)
    (define this-line '())
    (define (finish)
      (apply ht-append gap (reverse this-line)))
    (let loop ()
      (cond
        [(null? picts) 
         (finish)]
        [else
         (define pict (car picts))
         (cond
           [(< (pict-width pict) width)
            (set! this-line (cons pict this-line))
            (set! width (- width (pict-width pict) gap))
            (set! picts (cdr picts))
            (loop)]
           [else
            (vl-append 10
                       (finish)
                       (combine picts))])])))
  
  (slide
   (combine
    (for/list ([i (in-range 32)])
      (tree->pict (copy i) #f))))
  
  
  (define/contract (diff-path b m)
    ;; contract makes sure argument invariant holds
    (->i ([b (or/c node? #f)]
          [m (b) (λ (m) (<= m (size b) (+ m 1)))])
         any)
    (match* (b m)
      [(#f 0) '()]
      [((node _ #f #f _) 0) '(l)]
      [((node _ s t _) (? (and/c odd? non-zero?))) 
       (define k (/ (- m 1) 2))
       (cons 'l (diff-path s k))]
      [((node _ s t _) (? (and/c even? non-zero?)))
       (define k (/ (- m 2) 2))
       (cons 'r (diff-path t k))]))

  (slide 
   #:title "diff's path, n=m case"
   (combine
    (for*/list ([n (in-range 32)])
      (define b (copy n))
      (define d (diff-path b n))
      (tree->pict b d))))
  
  (slide 
   #:title "diff's path, n+1=m case"
   (combine
    (for*/list ([n (in-range 0 32)])
      (define b (copy n))
      (define d (diff-path b (max 0 (- n 1))))
      (tree->pict b d))))
  
  
  (define (plot-sum-of-logs upper-bound)
    (plot-pict
     #:x-label "n"
     #:y-label "sum_of_logs(n)"
     (lines 
      (for/list ([i (in-range upper-bound)])
        (vector i (sum-of-logs i))))))
  
  (slide 
   (scale-to-fit
    (vc-append
     (hc-append
      (plot-sum-of-logs (expt 2 8)) (plot-sum-of-logs (expt 2 9)))
     (hc-append
      (plot-sum-of-logs (expt 2 10)) (plot-sum-of-logs (expt 2 11))))
    client-w client-h)))
