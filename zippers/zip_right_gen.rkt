#lang at-exp s-exp tmonad
(provide zip_right)

(Fixpoint
 zip_right
 @A{Set} @z{Zipper A} @SOME_RIGHT{(snd z) <> nil}
 #:returns @{Zipper A}
 (match ((snd z))
   [(nil) => (<== _)]
   [(cons a ys) =>
    (<== (pair (cons a (fst z)) ys))]))
