#lang at-exp s-exp "tmonad.rkt"
(require "unravel.rkt")
(provide make_array_td)

(Fixpoint
 make_array_td #:implicit @A{Set} @xs{list A}
 #:measure "(length xs)"
 #:returns @{@"@"bin_tree A}
 (match (xs)
   [(nil) => (<== bt_mt)]
   [(cons x xs′)
    =>
    (bind ([eo (unravel xs′)])
          (match (eo)
            [(pair odds evens)
             =>
             (bind ([odds_bt (make_array_td odds)])
                   (bind ([evens_bt (make_array_td evens)])
                         (<== (bt_node x odds_bt evens_bt))))]))]))
