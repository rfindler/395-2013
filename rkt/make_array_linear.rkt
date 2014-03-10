#lang at-exp s-exp "tmonad.rkt"
(require "rows1.rkt" "fold.rkt" "build.rkt")

(provide make_array_linear)

(Fixpoint
 make_array_linear 
 #:implicit @A{Set}
 @xs{list A}
 #:returns @{@"@"bin_tree A}
 (bind ((the_rows (rows1 xs)))
       (bind ((built (foldr build (list bt_mt) the_rows)))
             (match (built)
               [(nil) => (<== bt_mt)]
               [(cons t ts′) => (<== t)]))))
