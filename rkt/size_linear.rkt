#lang at-exp s-exp "tmonad.rkt"

(Fixpoint
 size_linear @bt{@"@"bin_tree A}
 #:returns @{nat}
 (match bt
   [(bt_mt) => (<== 0)]
   [(bt_node x l r)
    =>
    (bind ([lsize (size_linear l)])
          (bind ([rsize (size_linear r)])
                (<== (+ lsize rsize 1))))]))

