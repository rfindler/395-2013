#lang at-exp s-exp tmonad/overly-specific
(provide drop)

(Fixpoint
 drop #:implicit @A{Set} @n{nat} @xs{list A}
 #:returns @{list A}
 (match (n)
   [0 => (<== xs)]
   [(S n′) 
    => 
    (match (xs)
      [(nil) => (<== nil)]
      [(cons x xs)
       => 
       (bind ([tl (drop n′ xs)])
             (<== tl))])]))
