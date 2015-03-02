#lang at-exp s-exp tmonad/overly-specific

(provide unravel)

(Fixpoint
 unravel #:implicit @A{Set} @xs{list A}
 #:returns @{list A * list A}
 (match (xs)
   [(nil) => (<== (pair nil nil))]
   [(cons x xs′)
    =>
    (bind ([odds_evens (unravel xs′)])
          (match (odds_evens)
            [(pair odds evens)
             =>
             (<== (pair (cons x evens) odds))]))]))
