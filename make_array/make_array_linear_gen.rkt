#lang at-exp s-exp tmonad
(require "rows1_gen.rkt" "../fold/fold_gen.rkt" "foldr_build_gen.rkt")

(provide make_array_linear)

(Fixpoint
 make_array_linear 
 #:implicit @A{Set}
 @xs{list A}
 #:returns @{@"@"bin_tree A}
 (bind ((the_rows (rows1 xs)))
       (bind ((built (foldr_build (cons bt_mt nil) the_rows)))
             (match (built)
               ;; this first case should never happen
               [(nil) => (<== bt_mt)]
               ;; ts′ should always be nil
               [(cons t ts′) => (<== t)]))))
