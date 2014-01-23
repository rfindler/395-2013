#lang racket
(require "braun.rkt" "log.rkt")

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


;; computes the running time of diff
(define/contract (diff-rt b m)
  ;; contract makes sure argument invariant holds
  (->i ([b (or/c node? #f)]
        [m (b) (λ (m) (<= m (size b) (+ m 1)))])
       any)
  (match* (b m)
    [(#f 0) 0]
    [((node _ #f #f _) 0) 1]
    [((node _ s t _) (? (and/c odd? non-zero?))) 
     (define k (/ (- m 1) 2))
     (+ (diff-rt s k) 1)]
    [((node _ s t _) (? (and/c even? non-zero?)))
     (define k (/ (- m 2) 2))
     (+ (diff-rt t k) 1)]))
(define (non-zero? n) (not (= n 0)))

(module+ test
  (printf "testing running time of diff\n")
  (for ([n (in-range 10)])
    (for ([m (in-list (list (- n 1) n))])
      (when (positive? m)
        (define bt (copy n))
        (define d (diff-rt bt m))
        (define f (+ (fl_log m) (diff bt m)))
        (unless (= d f)
          (eprintf "diff rt wrong: n = ~a m = ~a d = ~a f = ~a\n" n m d f))))))

;; compute the size according to Okasaki's algorithm
(define (loglog-size b)
  (match b
    [#f 0]
    [(node _ s t _) 
     (define m (loglog-size t))
     (+ 1 (* 2 m) (diff s m))]))
(define (diff b m) (- (size b) m))

(module+ test
  (printf "testing size vs loglog-size\n")
  (for ([i (in-range 1000)])
    (define b (copy i))
    (unless (= (size b) (loglog-size b))
      (error 'size-mismatch "i ~a (size b) ~s (loglog-size b) ~s"
             i (size b) (loglog-size b)))))

;; compute the running time of the loglog-size function
(define (loglog-size-rt b)
  (match b
    [#f 0]
    [(node _ s t _) 
     (define rt-t (loglog-size-rt t))
     (+ 1 rt-t (diff-rt s (size t)))]))

(define (sum-of-logs n)
  (cond
    [(zero? n) 0]
    [(odd? n) (+ (fl_log n) (sum-of-logs (div2 (- n 1))))]
    [(even? n) (+ (cl_log n) (sum-of-logs (div2 (- n 1))))]))

(module+ test
  (printf "testing sum-of-logs\n")
  (for ([n (in-range 200)])
    (define d (loglog-size-rt (copy n)))
    (define f (sum-of-logs n))
    (unless (= d f)
      (eprintf "size rt wrong: n = ~a d = ~a f = ~a\n" n d f))))

(define (sum-of-logs-lb n) (div2 (* (cl_log n) (fl_log n))))

(module+ test
  (printf "testing lower bound of sum-of-logs\n")
  (for ([n (in-range 0 10000000 10000)])
    (define lb (sum-of-logs-lb n))
    (define sl (sum-of-logs n))
    (unless (<= lb sl)
      (eprintf "lower bound wrong: n = ~a lb = ~a sl = ~a\n"
               n lb sl))))

(define (sum-of-logs-ub n) (* 2 (fl_log n) (fl_log n)))

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
