#lang at-exp s-exp "tmonad.rkt"

(provide insert)

#|

This language contains 'Fixpoint' 'provide' and
expressions of the shape below.

It implicitly defines a main module that emits
the corresponding Coq code and the functions, when
used back in regular racket (say 'insert') return two
values: the result of the function and the step count.

;; An exp is one of:
;;  (match <exp> (<pat> => <exp) ...)
;;  (if <exp> <exp> <exp>)
;;  (let ([<id> <exp>]) <exp>)
;;  (<mnid> <exp> ...)   -- call to a function that doesn't return something in the monad
;;  (<id> <exp> ...)     -- call to a function that returns        something in the monad
;;  <id>
;;  <constant>

;; A pat is either:
;;  <id>
;;  (<id> <id> ...)

(still plenty of work to do here)

|#


(Fixpoint 
 insert #:implicit A @i{A} @b{@"@"bin_tree A}
 #:returns @{@"@"bin_tree A}
 (match b 
   [bt_mt => (bt_node i bt_mt bt_mt)]
   [(bt_node j s t) => (bt_node i (insert j t) s)]))
 
#|
#;
(Fixpoint
 make_array_naive #:implicit A @{}
 (match xs
   [nil => bt_mt]
   [(cons x xs′)
    =>
    (insert x (make_array_naive xs′))]))


#;
(out-exp 
 `(match n
    [0 => (pair (bt_node x bt_mt bt_mt) bt_mt)]
    [(S n′)
     =>
     (let ([pr (copy2 (div2 n′))])
       (match pr
         [(pair s t) 
          => 
          (if (even_odd_dec n′)
              (pair (bt_node x s t) (bt_node x t t))
              (pair (bt_node x s s) (bt_node x s t)))]))]))
|#