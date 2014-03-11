#lang at-exp s-exp "tmonad.rkt"
(require "build.rkt")

(provide foldr_build)

(Fixpoint
 foldr_build #:implicit @A{Set} @base{list (@"@"bin_tree A)} @l{list (nat * list A)}
 #:returns @{list (@"@"bin_tree A)}
 (match (l)
   [(nil) => (<== base)]
   [(cons x xs)
    =>
    (bind ((acc (foldr_build base xs)))
          (bind ((out (build x acc)))
                (<== out)))]))
