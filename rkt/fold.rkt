#lang at-exp s-exp "tmonad.rkt"

(Fixpoint
 foldr @f{f_type} @base{B} @PFbase{P base nil 3} @l{list A}
 #:returns @{B}
 (match l 
   [(nil) => (<== base)]
   [(cons x xs)
    =>
    (bind ((acc (foldr f base PFbase xs)))
          (bind ((out (f x acc)))
                (<== out)))]))
