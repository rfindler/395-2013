#lang at-exp s-exp tmonad
(provide from_zip)

(Fixpoint
 from_zip
 @A{Set} @z{Zipper A} @ALL_RIGHT{(fst z) = nil}
 #:returns @{list A}
 (<== (snd z)))