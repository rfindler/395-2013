#lang racket
(require "braun.rkt")

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
  (require slideshow "pict.rkt")
  
  (slide 
   (apply 
    para
    #:width 800
    (for/list ([i (in-range 32)])
      (tree->pict (naive-make-array (build-list i values))
                  #f)))))