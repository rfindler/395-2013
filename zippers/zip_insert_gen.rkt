#lang at-exp s-exp tmonad
(provide zip_insert)

(Fixpoint
 zip_insert
 @A{Set} @z{Zipper A} @a{A}
 #:returns @{Zipper A}
 (<== (pair (fst z) (cons a (snd z)))))