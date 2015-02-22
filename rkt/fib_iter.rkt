#lang at-exp s-exp "tmonad.rkt"

(require "fib_iter_loop.rkt")

(Fixpoint
 fib_iter @target{nat} 
  #:returns @{nat}
 (match (target)
   [0 => (<== 1)]
   [(S target′)
    => 
    (match (target′)
      [0 => (<== 1)]
      [(S target′′)
       =>
       (bind ((res (fib_iter_loop target′ target 1 1)))
             (<== res))])]))
