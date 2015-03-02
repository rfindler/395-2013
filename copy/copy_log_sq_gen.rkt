#lang at-exp s-exp tmonad/overly-specific
(require "../insert/insert_log_gen.rkt")
(provide copy_log_sq)
(Fixpoint
 copy_log_sq #:implicit @A{Set} @x{A} @n{nat}
 #:measure n
 #:returns @{bin_tree}
 (match (n)
   [0 => (<== bt_mt)]
   [(S n′) 
    => 
    (bind ((t (copy_log_sq x (div2 n′))))
          (if (even_odd_dec n′)
              (<== (bt_node x t t))
              (bind ((s (insert x t)))
                    (<== (bt_node x s t)))))]))
