#lang at-exp s-exp "tmonad.rkt"

(Fixpoint
 fib_rec @n{nat} 
  #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S n′) 
    => 
    (match (n′)
      [0 => (<== 1)]
      [(S n′′)
       =>
       (bind ((a (fib_rec n′′)))
             (bind ((b (fib_rec n′)))
                   (<== (+ a b))))])]))
