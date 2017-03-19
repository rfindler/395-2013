#lang at-exp s-exp tmonad/overly-specific

(Fixpoint
 size_linear @bt{@"@"bin_tree A}
 #:returns @{nat}
 (match (bt)
   [(bt_mt) => (<== 0)]
   [(bt_node x l r)
    =>
    (bind ([ls (size_linear l)])
          (bind ([rs (size_linear r)])
                (<== (+ ls rs 1))))]))

