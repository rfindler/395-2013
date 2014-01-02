#lang racket
(require "braun.rkt" "log.rkt")

(module+ slideshow (require slideshow plot "pict.rkt"))

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
  (slide 
   (apply 
    para
    #:width 800
    (for/list ([i (in-range 32)])
      (tree->pict (naive-make-array (build-list i values))
                  #f)))))

(define (unravel+time l)
  (cond
    [(null? l) (values '() '() 0)]
    [else
     (define-values (odds evens time) (unravel+time (cdr l)))
     (values (cons (car l) evens) odds (+ time 1))]))

(define (td-make-array+time l)
  (cond
    [(null? l) (values #f 0)]
    [else 
     (define-values (odds evens time1) (unravel+time (cdr l)))
     (define-values (left time2) (td-make-array+time odds))
     (define-values (right time3) (td-make-array+time evens))
     (values (mknode #:val (car l) left right)
             (+ time1 time2 time3 1))]))

(define (td-make-array l)
  (define-values (bt time) (td-make-array+time l))
  bt)

(module+ test 
  (printf "testing td-make-array against naive-make-array\n")
  (let ()
    (define l '())
    (for ([i (in-range 1024)])
      (unless (equal? (td-make-array l)
                      (naive-make-array l))
        (error 'td-make-array "disagrees with naive-make-array for ~s" l))
      (set! l (cons i l)))))

(define (td-make-array-time l)
  (define-values (bt time) (td-make-array+time l))
  time)

(define (td-make-array-time2 len)
  (cond
    [(zero? len) 0]
    [else
     (+ (td-make-array-time2 (div2 len))
        (td-make-array-time2 (div2 (- len 1)))
        len)]))

(module+ test 
  (printf "testing td-make-array's time\n")
  (let ()
    (define l '())
    (for ([i (in-range 1024)])
      (define real-time (td-make-array-time l))
      (define hoped-for-time (td-make-array-time2 i))
      (unless (equal? real-time hoped-for-time)
        (error 'td-make-array-time
               "disagrees with naive-make-array for ~s: real ~s hoped-for ~s" 
               i
               real-time
               hoped-for-time))
      (set! l (cons i l)))))

(module+ slideshow
  (require (only-in math fllog2))
  (define (plot-td-make-array-time upper-bound)
    (plot-pict
     #:x-label "n"
     #:y-label "make_array_time(n) & n*cl_log(n)"
     (list
      (lines 
       (for/list ([n (in-range upper-bound)])
         (vector n (td-make-array-time2 n))))
      (lines 
       #:color "red"
       (for/list ([n (in-range upper-bound)])
         (vector n (* n (cl_log n))))))))
  
  (slide 
   (scale-to-fit
    (hc-append 40
               (plot-td-make-array-time (expt 2 11))
               (plot-td-make-array-time 10))
    client-w client-h)))
