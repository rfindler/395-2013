#lang at-exp s-exp "tmonad.rkt"
(require "drop.rkt" "take.rkt")
(provide rows)

(Fixpoint
 rows #:implicit @A{Set} @k{nat} @xs{list A}
 #:measure "(length xs)"
 #:returns @{list (nat * (list A))}
 (match (k)
   [0 => (<== nil)]
   [(S _) 
    =>
    (match (xs)
      [(nil) => (<== nil)]
      [(cons _ _)
       => 
       (bind ([taken (take k xs)])
             (bind ([dropped (drop k xs)])
                   (bind ([rst (rows (* 2 k) dropped)])
                         (<== (cons (pair k taken) rst)))))])]))
