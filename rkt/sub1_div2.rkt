#lang at-exp s-exp tmonad/overly-specific
(provide sub1_div2)
(require "../arith/sub1_gen.rkt")

(Fixpoint
 sub1_div2 @n{nat}
 #:measure n
 #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S _) 
    =>
    (bind ([nn (sub1 n)])
          (bind ([pr (sub1_div2 (div2 nn))])
                (<== pr)))]))
