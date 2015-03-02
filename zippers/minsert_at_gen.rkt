#lang at-exp s-exp tmonad/overly-specific
(require "insert_at_gen.rkt")
(provide minsert_at)

(Fixpoint
 minsert_at
 @A{Set} @ma{list A} @n{nat} @l{list A} @NV{n <= length l}
 #:returns @{list A}
 (match (ma)
   [(nil) => (<== l)]
   [(cons a map) =>
    (bind ([resp (insert_at A a n l NV)])
          (bind ([respp (minsert_at A map n resp _)])
                (<== respp)))]))
