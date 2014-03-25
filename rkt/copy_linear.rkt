#lang at-exp s-exp "tmonad.rkt"

(provide copy_linear)
(Fixpoint
 copy_linear #:implicit @A{Set} @x{A} @n{nat}
 #:measure n
 #:returns @{bin_tree}
 (match (n)
   [0 => (<== bt_mt)]
   [(S n′) 
    => 
    (bind ((l (copy_linear x (div2 n))))
          (bind ((r (copy_linear x (div2 n′))))
                (<== (bt_node x l r))))]))
