#lang at-exp s-exp tmonad/overly-specific
(provide cinterleave)

(Fixpoint
 cinterleave @A{Set} @e{list A} @o{list A}
 #:measure "(length (e ++ o))"
 #:returns @{list A}
 (match (e)
   [(nil) => (<== o)]
   [(cons x xs) =>
    (bind ([xsp (cinterleave A o xs)])
          (<== (cons x xsp)))]))
