#lang at-exp s-exp "tmonad.rkt"
(require "zip_with_3_bt_node.rkt"
         "pad_drop.rkt"
         "split.rkt")

(provide build)

(Fixpoint
 build 
 #:implicit @A{Set}
 @pr{nat * list A}
 @ts{list (@"@"bin_tree A)}
 #:returns @{list (@"@"bin_tree A)}
 (match (pr)
   [(pair k xs)
    =>
    (bind ([padded (pad_drop (* 2 k) ts bt_mt)])
          (bind ([ts1ts2 (split k padded)])
                (match (ts1ts2)
                  [(pair ts1 ts2)
                   =>
                   (bind ([zipped (zip_with_3_bt_node xs ts1 ts2)])
                         (<== zipped))])))]))
