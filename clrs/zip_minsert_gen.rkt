#lang at-exp s-exp tmonad
(require "zip_insert_gen.rkt")
(provide zip_minsert)

(Fixpoint
 zip_minsert
 @A{Set} @ma{list A} @z{Zipper A}
 #:returns @{Zipper A}
 (match (ma)
   [(nil) => (<== z)]
   [(cons a map) =>
    (bind ([zp (zip_insert A z a)])
          (bind ([zpp (zip_minsert A map zp)])
                (<== zpp)))]))
