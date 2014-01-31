#lang at-exp s-exp "tmonad.rkt"
(provide sub1)

(Fixpoint
 sub1 @n{nat}
 #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S _) 
    =>
    (if (even_odd_dec n)
        (bind ((sd2 (sub1 (div2 n))))
              (<== (+ sd2 sd2 1)))
        
        ;; this is not really subtraction; 
        ;; it is masking the last bit (since
        ;; we know that the number is odd), 
        ;; so it is okay to have something with 
        ;; a constant cost here.
        (<== (- n 1)))]))
