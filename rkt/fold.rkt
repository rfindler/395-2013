#lang at-exp s-exp "tmonad.rkt"

(Fixpoint
 foldr @f{f_type} @base{base_type} @l{list A}
 #:returns @{B}
 (match l 
   [(nil) => (<== (proj1_sig base))]
   [(cons x xs)
    =>
    (bind ((acc (foldr f base xs)))
          (bind ((out (f x acc)))
                (<== out)))]))
