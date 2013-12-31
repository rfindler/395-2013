#lang racket
;; this file is used to figure out what the running time actually is for diff

;; a braun tree is either #f or (node any braun-tree bran-tree nat)
(struct node (v l r s) #:transparent)

(define (size n)
  (cond
    [(node? n) (node-s n)]
    [else 0]))

(define (mknode l r #:val [v #f])
  (unless (<= (size r) (size l) (+ (size r) 1))
    (error 'mknode "invariant check failed:\n  (size l) = ~s   l = ~s\n  (size r) = ~s   r = ~s" 
           (size l) l
           (size r) r))
  (node v l r (+ (size l) (size r) 1)))

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
  (for ([i (in-range 1000)]) (copy i)))

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

(define (div2 n) (quotient n 2))

#;
(define (fl_log n)
  (cond
    [(zero? n) 0]
    [else (+ (fl_log (div2 (- n 1))) 1)]))

#;
(define (cl_log n)
  (cond
    [(zero? n) 0]
    [else (+ (cl_log (div2 n)) 1)]))

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

  (printf "testing running time of diff\n")
  (for ([n (in-range 10)])
    (for ([m (in-list (list (- n 1) n))])
      (when (positive? m)
        (define d (diff-rt (copy n) m))
        (define f (if (= n m)
                      (fl_log n)
                      (cl_log n)))
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

(define (insert x bt)
  (match bt
    [#f (mknode #:val x #f #f)]
    [(node y s t _) (mknode #:val x (insert y t) s)]))

(define (naive-make-array xs) 
  (cond
    [(null? xs) #f]
    [else 
     (insert (car xs) (naive-make-array (cdr xs)))]))

(define (index bt i)
  (match bt
    [(node x s t _)
     (cond
       [(zero? i) x]
       [(odd? i) (index s (/ (- i 1) 2))]
       [(even? i) (index t (/ (- i 2) 2))])]))

(module+ test
  (printf "testing naive-make-array+index\n")
  (for ([size (in-range 1000)])
    (define bt (naive-make-array (build-list size values)))
    (for ([i (in-range size)])
      (define i2 (index bt i))
      (unless (= i i2)
        (error 'naive-make-array+index "bt size ~a index ~a, got ~a"
               size
               i
               i2)))))

(define (keep-evens l)
  (match l
    ['() '()]
    [(cons x xs)
     (match xs
       ['() (cons x '())]
       [(cons y ys) (cons x (keep-evens ys))])]))

(define (keep-odds l)
  (match l
    ['() '()]
    [(cons x xs)
     (keep-evens xs)]))

(define (make-array-even-odd-property x ls)
  (define s1 (naive-make-array (keep-evens ls)))
  (define t1 (naive-make-array (keep-odds ls)))
  (match (naive-make-array (cons x ls))
    [(node x s2 t2 _) 
     (and (equal? s1 s2)
          (equal? t1 t2))]
    [else #f]))

(module+ test
  (printf "testing make-array-even-odd-property\n")
  (for ([x (in-range 512)])
    (unless (make-array-even-odd-property 0 (build-list x add1))
      (error 'make-array-even-odd-property "failed for size ~a" x))))

(module+ slideshow
  (require slideshow plot)
  
  (define (tree->pict t path)
    (match t
      [#f (define b (blank))
          (refocus (cc-superimpose b (filled-ellipse 5 5))
                   b)]
      [(node val l r _) 
       (define which-way (and (pair? path) (car path)))
       (define lp (tree->pict l (and (equal? which-way 'l) (cdr path))))
       (define rp (tree->pict r (and (equal? which-way 'r) (cdr path))))
       (define main (vc-append (if val 
                                   (colorize (inset (text (format "~s" val)) 0 -4 0 4) "DarkGreen")
                                   (blank 0 10))
                               (ht-append 10 lp rp)))
       (define left-arrow (launder
                           (pin-line 
                            (ghost main)
                            main ct-find
                            lp ct-find)))
       (define right-arrow (launder
                            (pin-line 
                             (ghost main)
                             main ct-find
                             rp ct-find)))
       (ct-superimpose (linewidth 2 
                                  (if (equal? which-way 'l)
                                      (colorize left-arrow "red")
                                      (colorize left-arrow (if val "gray" "black"))))
                       (linewidth 2
                                  (if (equal? which-way 'r) 
                                      (colorize right-arrow "red")
                                      (colorize right-arrow (if val "gray" "black"))))
                       main)]))
  
  (slide 
   (apply 
    para
    #:width 800
    (for/list ([i (in-range 32)])
      (tree->pict (naive-make-array (build-list i values))
                  #f))))
  
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
