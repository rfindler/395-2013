#lang at-exp s-exp "tmonad.rkt"
(require "rows.rkt")
(provide rows1)

(Fixpoint
 rows1 #:implicit @A{Set} @xs{list A}
 #:returns @{list (nat * (list A))}
 (bind ((res (rows 1 xs)))
       (<== res)))
