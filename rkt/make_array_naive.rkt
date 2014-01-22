#lang at-exp s-exp "tmonad.rkt"

(require "insert.rkt")

(Fixpoint
 make_array_naive #:implicit @A{Set} @xs{list A}
 #:returns @{@"@"bin_tree A}
 (match xs
   [(nil) => (<== bt_mt)]
   [(cons x xs′)
    =>
    (bind ([bt (make_array_naive xs′)])
      (insert x bt))]))
