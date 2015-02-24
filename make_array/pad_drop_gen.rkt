#lang at-exp s-exp tmonad
(provide pad_drop)
(Fixpoint
 pad_drop #:implicit @A{Set} @k{nat} @xs{list A} @x{A}
 #:returns @{list A}
 (match (k)
   [0 => (<== nil)]
   [(S k′) 
    =>
    (match (xs)
      [(nil) 
       =>
       (bind ([rst (pad_drop k′ nil x)])
             (<== (cons x rst)))]
      [(cons hd tl)
       =>
       (bind ([rst (pad_drop k′ tl x)])
             (<== (cons hd rst)))])]))
