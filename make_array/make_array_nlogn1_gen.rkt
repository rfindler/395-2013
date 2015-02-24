#lang at-exp s-exp tmonad
(require "../insert/insert_log_gen.rkt")
(provide make_array_naive)

(Fixpoint
 make_array_naive #:implicit @A{Set} @xs{list A}
 #:returns @{@"@"bin_tree A}
 (match (xs)
   [(nil) => (<== bt_mt)]
   [(cons x xs′)
    =>
    (bind ([bt (make_array_naive xs′)])
          (bind ([ir (insert x bt)])
                (<== ir)))]))
