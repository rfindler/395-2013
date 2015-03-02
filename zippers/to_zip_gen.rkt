#lang at-exp s-exp tmonad/overly-specific
(provide to_zip)

(Fixpoint
 to_zip
 @A{Set} @l{list A}
 #:returns @{Zipper A}
 (<== (pair nil l)))
