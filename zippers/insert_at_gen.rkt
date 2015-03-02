#lang at-exp s-exp tmonad/overly-specific
(provide insert_at)

(Fixpoint
 insert_at
 @A{Set} @a{A} @n{nat} @l{list A} @NV{n <= length l}
 #:returns @{list A}
 (match (n)
   [O =>
    (<== (cons a l))]
   [(S np) =>
    (match (l)
      [(nil) => (<== _)]
      [(cons ap lp) =>
       (bind ([resp (insert_at A a np lp _)])
             (<== (cons ap resp)))])]))
