#lang at-exp s-exp tmonad
(require "fib_iter_loop_gen.rkt")

(Fixpoint
 fib_iter @target{nat} 
  #:returns @{nat}
 (match (target)
   [0 => (<== 0)]
   [(S target′)
    => 
    (match (target′)
      [0 => (<== 1)]
      [(S target′′)
       =>
       (bind ((res (fib_iter_loop target′ target 0 1)))
             (<== res))])]))
