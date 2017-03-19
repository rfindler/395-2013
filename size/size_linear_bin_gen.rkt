#lang at-exp s-exp tmonad/overly-specific

(provide size_linear_bin)

(Fixpoint
 size_linear_bin @bt{@"@"bin_tree A}
 #:returns @{nat}
 (match (bt)
   [(bt_mt) => (<== 0)]
   [(bt_node x l r)
    =>
    (bind ([ls (size_linear_bin l)])
          (bind ([rs (size_linear_bin r)])
                (if (even_odd_dec ls)
                    (if (even_odd_dec rs)
                        (<== (double_plus1 ls))
                        (<== (double ls)))
                    (if (even_odd_dec rs)
                        (<== (double ls))
                        (<== (double_plus1 ls))))))]))
