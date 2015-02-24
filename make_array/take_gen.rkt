#lang at-exp s-exp tmonad
(provide take)

(Fixpoint
 take #:implicit @A{Set} @n{nat} @xs{list A}
 #:returns @{list A}
 (match (xs)
   [(nil) => (<== nil)]
   [(cons x xs)
    =>
    (match (n)
      [0 => (<== nil)]
      [(S n′) => 
              (bind ([rst (take n′ xs)])
                    (<== (cons x rst)))])]))
