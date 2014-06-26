#lang at-exp s-exp "tmonad.rkt"
(provide sub1_div2)
(require "sub1.rkt")


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