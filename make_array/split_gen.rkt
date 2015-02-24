#lang at-exp s-exp tmonad
(provide split)
(require "take_gen.rkt" "drop_gen.rkt")
(Fixpoint
 split #:implicit @A{Set} @k{nat} @xs{list A}
 #:returns @{list A * list A}
 (bind ((taken (take k xs)))
       (bind ((dropped (drop k xs)))
             (<== (pair taken dropped)))))
