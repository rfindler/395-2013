#lang at-exp s-exp tmonad

(provide split2)

(Fixpoint
 split2 #:implicit @A{Set}
 @n{nat} @l{list A}
 @V{n <= length l} 
 #:returns @{((list A) * (list A))}
 (match (n)
   [0 => (<== (pair nil l))]
   [(S n′)
    =>
    (match (l)
      [(nil) => (<== _)]
      [(cons a l′)
       =>
       (bind ((res (split2 n′ l′ _)))
             (<== (pair (cons a (fst res)) (snd res))))])]))
