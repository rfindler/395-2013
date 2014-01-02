#lang racket
(require pict "braun.rkt")

(provide (all-defined-out))

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

;; no tests
(module test racket/base)