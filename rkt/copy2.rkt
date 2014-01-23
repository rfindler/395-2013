#lang at-exp s-exp "tmonad.rkt"

(provide copy2)

(Fixpoint
 copy2 #:implicit @A{Set} @x{A} @n{nat}
 #:measure n
 #:returns @{@"@"bin_tree A * @"@"bin_tree A}
 (match n
   [0 => (<== (pair (bt_node x bt_mt bt_mt) bt_mt))]
   [(S n′) 
    =>
    (bind ([pr (copy2 x (div2 n′))])
      (match pr
        [(pair s t) 
         => 
         (if (even_odd_dec n′)
             (<== (pair (bt_node x s t) (bt_node x t t)))
             (<== (pair (bt_node x s s) (bt_node x s t))))]))]))
