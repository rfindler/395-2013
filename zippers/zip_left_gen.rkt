#lang at-exp s-exp tmonad/overly-specific
(provide zip_left)

(Fixpoint
 zip_left
 @A{Set} @z{Zipper A} @SOME_LEFT{(fst z) <> nil}
 #:returns @{Zipper A}
 (match ((fst z))
   [(nil) => (<== _)]
   [(cons b xs) =>
    (<== (pair xs (cons b (snd z))))]))
