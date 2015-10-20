#lang at-exp s-exp tmonad
(provide tmult)
(require "plus_gen.rkt")

(Fixpoint
 tmult @n{nat} @m{nat}
 #:measure n
 #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S _)
    =>
    (if (even_odd_dec n)
        (bind ([md2 (tmult (div2 n) m)])
              (<== (double md2)))
        (bind ([md2 (tmult (div2 n) m)])
          (bind ([res (tplus m (double md2))])
              (<== res))))]))


        