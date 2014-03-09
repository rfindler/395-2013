#lang at-exp s-exp "tmonad.rkt"
(provide split)
(require "take.rkt" "drop.rkt")
(Fixpoint
 split #:implicit @A{Set} @k{nat} @xs{list A}
 #:returns @{list A * list A}
 (bind ((taken (take k xs)))
       (bind ((dropped (drop k xs)))
             (<== (pair taken dropped)))))
