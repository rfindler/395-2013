#lang at-exp s-exp tmonad/overly-specific
(require "zip_left_gen.rkt")
(provide zip_leftn)

(Fixpoint
 zip_leftn
 @A{Set} @n{nat} @z{Zipper A} @NV{n <= length (fst z)}
 #:returns @{Zipper A}
 (match (n)
   [O => (<== z)]
   [(S np) =>
    (bind ([zp (zip_left A z _)])
          (bind ([zpp (zip_leftn A np zp _)])
                (<== zpp)))]))
