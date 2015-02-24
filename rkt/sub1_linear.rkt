#lang at-exp s-exp tmonad
(require "../sub1/sub1_gen.rkt")
(provide sub1_linear)

(Fixpoint
 sub1_linear @n{nat}
 #:measure n
 #:returns @{nat}
 (match (n)
   [0 => (<== 0)]
   [(S _) 
    =>
    (bind ((nn (sub1 n)))
          (bind ((nnn (sub1_linear nn)))
                (<== 0)))]))
