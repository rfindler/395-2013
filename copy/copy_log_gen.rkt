#lang at-exp s-exp tmonad

(require "copy2_gen.rkt")

(Fixpoint
 copy #:implicit @A{Set} @x{A} @n{nat}
 #:returns @{@"@"bin_tree A}
 (bind ([pr (copy2 x n)])
       (match (pr)
         [(pair s t) => (<== t)])))

(provide copy)

