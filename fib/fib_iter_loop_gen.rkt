#lang at-exp s-exp tmonad

(provide fib_iter_loop)

(Fixpoint
 fib_iter_loop @fuel{nat} @target{nat} @a{nat} @b{nat} 
 #:returns @{nat}
 (match (fuel)
   [0 => (<== b)]
   [(S fuel) 
    =>
    (bind ((res (fib_iter_loop fuel target b (+ a b))))
          (<== res))]))
