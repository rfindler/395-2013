#lang at-exp s-exp "tmonad.rkt"

;; this is broken in strange ways
;; 1) switching the order of the cases doesn't work.

(require "insert.rkt")

(Fixpoint
 make_array_naive #:implicit A @xs{list A}
 #:returns @{@"@"bin_tree A}
 (match xs
   [nil => (<== bt_mt)]
   [(cons x xs′)
    =>
    (bind ([bt (make_array_naive xs′)])
      (insert x bt))]))
