#lang at-exp s-exp tmonad
(require "../arith/plus_gen.rkt")
(provide fib_iter_loop)

(Fixpoint
 fib_iter_loop @fuel{nat} @target{nat} @a{nat} @b{nat} 
 #:returns @{nat}
 (match (fuel)
   [0 => (<== b)]
   [(S fuel) 
    =>
    (bind ((sum (tplus a b)))
          (bind ((res (fib_iter_loop fuel target b sum)))
                (<== res)))]))
