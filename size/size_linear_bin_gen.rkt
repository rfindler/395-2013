#lang at-exp s-exp tmonad/overly-specific

(provide size_linear_bin)

(Fixpoint
 size_linear_bin @bt{@"@"bin_tree A}
 #:returns @{nat}
 (match (bt)
   [(bt_mt) => (<== 0)]
   [(bt_node x l r)
    =>
    (bind ([lsize (size_linear_bin l)])
          (bind ([rsize (size_linear_bin r)])
                (if (even_odd_dec lsize)
                    (if (even_odd_dec rsize)
                        (<== (double_plus_one lsize))
                        (<== (double lsize)))
                    (if (even_odd_dec rsize)
                        (<== (double lsize))
                        (<== (double_plus_one lsize))))))]))
