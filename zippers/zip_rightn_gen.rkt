#lang at-exp s-exp tmonad/overly-specific
(require "zip_right_gen.rkt")
(provide zip_rightn)

(Fixpoint
 zip_rightn
 @A{Set} @n{nat} @z{Zipper A} @NV{n <= length (snd z)}
 #:returns @{Zipper A}
 (match (n)
   [O => (<== z)]
   [(S np) =>
    (bind ([zp (zip_right A z _)])
          (bind ([zpp (zip_rightn A np zp _)])
                (<== zpp)))]))
