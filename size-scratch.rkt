#lang racket
;; this file is used to figure out what the running time actually is for diff

;; a braun tree is either #f or (node braun-tree bran-tree nat)
(struct node (l r s) #:transparent)

(define (size n)
  (cond
    [(node? n) (node-s n)]
    [else 0]))

(define (mknode l r)
  (unless (<= (size r) (size l) (+ (size r) 1))
    (error 'mknode "invariant check failed:\n  (size l) = ~s   l = ~s\n  (size r) = ~s   r = ~s" 
           (size l) l
           (size r) r))
  (node l r (+ (size l) (size r) 1)))

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

;; check no invariants break for 'copy'
(for ([i (in-range 1000)]) (copy i))

;; computes the running time of diff
(define/contract (diff-rt b m)
  ;; contract makes sure argument invariant holds
  (->i ([b (or/c node? #f)]
        [m (b) (λ (m) (<= m (size b) (+ m 1)))])
       any)
  (match* (b m)
    [(#f 0) 1]
    [((node #f #f _) 0) 1]
    [((node s t _) (? (and/c odd? non-zero?))) 
     (define k (/ (- m 1) 2))
     (+ (diff-rt s k) 1)]
    [((node s t _) (? (and/c even? non-zero?)))
     (define k (/ (- m 2) 2))
     (+ (diff-rt t k) 1)]))
(define (non-zero? n) (not (= n 0)))

(define (fl_log n)
  (cond
    [(zero? n) 0]
    [else (+ (fl_log (quotient (- n 1) 2)) 1)]))

(unless (equal? (map fl_log '(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15))
                '(0 1 1 2 2 2 2 3 3 3 3 3 3 3 3 4))
  (error 'fl_log "wrong"))

;; check running time of diff
(for ([n (in-range 1000)])
  (for ([m (in-list (list (- n 1) n))])
    (when (positive? m)
      (define d (diff-rt (copy n) m))
      (define f (+ (fl_log m) 1))
      (unless (= d f)
        (eprintf "diff rt wrong: n = ~a m = ~a d = ~a f = ~a\n" n m d f)))))

;; compute the size according to Okasaki's algorithm
(define (loglog-size b)
  (match b
    [#f 0]
    [(node s t _) 
     (define m (loglog-size t))
     (+ 1 (* 2 m) (diff s m))]))
(define (diff b m) (- (size b) m))

;; check that two size algorithms match up
(for ([i (in-range 1000)])
  (define b (copy i))
  (unless (= (size b) (loglog-size b))
    (error 'size-mismatch "i ~a (size b) ~s (loglog-size b) ~s"
           i (size b) (loglog-size b))))


;; compute the running time of the loglog-size function
(define (loglog-size-rt b)
  (match b
    [#f 1]
    [(node s t _) 
     (define rt-t (loglog-size-rt t))
     (+ 1 rt-t (diff-rt s (size t)))]))

;; hmm..... how to describe this in terms of 'n'?!
(for ([n (in-range 10)])
  (define d (loglog-size-rt (copy n)))
  (define f (* (fl_log n) (+ (fl_log n) 1))) ;; wrong!
  (unless (= d f)
    (eprintf "size rt wrong: n = ~a d = ~a f = ~a\n" n d f)))

(module+ slideshow
  (require slideshow)
  
  (define (tree->pict t)
    (match t
      [#f (define b (blank))
          (refocus (cc-superimpose b (filled-ellipse 5 5))
                   b)]
      [(node l r _) 
       (define lp (tree->pict l))
       (define rp (tree->pict r))
       (define main (vc-append (blank 0 10) (ht-append 10 lp rp)))
       (pin-line 
        (pin-line 
         main
         main ct-find
         rp ct-find)
        main ct-find
        lp ct-find)]))
  
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
    (for/list ([i (in-range 24)])
      (tree->pict (copy i))))))
