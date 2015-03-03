#lang at-exp s-exp tmonad

(require "plus_cin_gen.rkt")

(provide tplus)

(Fixpoint
 tplus @n{nat} @m{nat}
 #:returns @{nat}
 (bind ((res (plus_cin n m false)))
       (<== res)))


