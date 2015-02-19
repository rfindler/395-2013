#lang at-exp s-exp "tmonad.rkt"

(provide clength)
(Fixpoint
 clength #:implicit @A{Set} @l{list A}
 #:returns @{nat}
 (match (l)
   [(nil) => (<== 0)]
   [(cons a′ l′)
    => 
    (bind ((n′ (clength l′)))
          (<== (+ n′ 1)))]))

