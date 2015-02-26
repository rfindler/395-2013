#lang at-exp s-exp tmonad

(Fixpoint
 to_list_naive @A{Set} @b{@"@"bin_tree A}
 #:returns @{list A}
 (match (b)
   [(bt_mt) => (<== nil)]
   [(bt_node x s t)
    =>
    (bind ([sl (to_list_naive A s)])
          (bind ([tl (to_list_naive A t)])
                (bind ([xs (cinterleave A sl tl)])
                      (<== (cons x xs)))))]))
