#lang at-exp s-exp "tmonad.rkt"
(require "insert.rkt")
(provide copy_insert)
(Fixpoint
 copy_insert #:implicit @A{Set} @x{A} @n{nat}
 #:measure n
 #:returns @{bin_tree}
 (match (n)
   [0 => (<== bt_mt)]
   [(S n′) 
    => 
    (bind ((t (copy_insert x (div2 n′))))
          (if (even_odd_dec n′)
              (<== (bt_node x t t))
              (bind ((s (insert x t)))
                    (<== (bt_node x s t)))))]))
