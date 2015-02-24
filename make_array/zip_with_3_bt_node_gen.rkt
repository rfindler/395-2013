#lang at-exp s-exp tmonad
(provide zip_with_3_bt_node)

(Fixpoint
 zip_with_3_bt_node 
 #:implicit @A{Set}
 @xs{list A}
 @ts1{list (@"@"bin_tree A)}
 @ts2{list (@"@"bin_tree A)}
 #:returns @{list (@"@"bin_tree A)}
 (match (xs)
   [(nil) => (<== nil)]
   [(cons x xs′)
    =>
    (match (ts1)
      [(nil) => (<== nil)]
      [(cons t1 ts1′)
       =>
       (match (ts2)
         [(nil) => (<== nil)]
         [(cons t2 ts2′)
          =>
          (bind ([rest (zip_with_3_bt_node xs′ ts1′ ts2′)])
                (<== (cons (bt_node x t1 t2)
                           rest)))])])]))
