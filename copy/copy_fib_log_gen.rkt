#lang at-exp s-exp tmonad/overly-specific

(Fixpoint
 copy_fib @x{A} @n{nat}
 #:measure n
 #:returns @{bin_tree}
 (match (n)
   [0 => (<== bt_mt)]
   [_
    =>
    (if (even_odd_dec n)
        (bind ([l (copy_fib x (div2 n))])
              (bind ([r (copy_fib x (- (div2 n) 1))])
                    (<== (bt_node x l r))))
        (bind ([t (copy_fib x (div2 n))])
              (<== (bt_node x t t))))]))
