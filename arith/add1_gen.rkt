#lang at-exp s-exp tmonad/overly-specific
(provide add1)

(Fixpoint
 add1 @n{nat}
 #:measure n
 #:returns @{nat}
 (match (n)
   [0 => (<== 1)]
   [(S _) 
    =>
    (if (even_odd_dec n)
        ;; this is not really addition; 
        ;; it is and'ing the last bit (since
        ;; we know that the number is even), 
        (<== (+ n 1))
        (bind ((sd2 (add1 (div2 n))))
              (<== (+ sd2 sd2))))]))
