#lang at-exp s-exp tmonad
(provide rbt_blacken)

(Fixpoint
 rbt_blacken #:implicit @A{Set}
 @ct{CTree A}
 #:returns @{CTree A}
 (match (ct)
   [(CT_leaf)
    =>
    (<== ct)]
   [(CT_node l c v r)
    =>    
    (<== (CT_node l BLACK v r))]))
