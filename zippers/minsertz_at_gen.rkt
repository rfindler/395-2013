#lang at-exp s-exp tmonad
(require "to_zip_gen.rkt"
         "zip_rightn_gen.rkt"
         "zip_minsert_gen.rkt"
         "zip_leftn_gen.rkt"
         "from_zip_gen.rkt")
(provide minsertz_at)

(Fixpoint
 minsertz_at
 @A{Set} @ma{list A} @n{nat} @l{list A} @NV{n <= length l}
 #:returns @{list A}
 (bind ([z (to_zip A l)])
       (bind ([zr (zip_rightn A n z _)])
             (bind ([zrp (zip_minsert A ma zr)])
                   (bind ([zp (zip_leftn A n zrp _)])
                         (bind ([lp (from_zip A zp _)])
                               (<== lp)))))))
