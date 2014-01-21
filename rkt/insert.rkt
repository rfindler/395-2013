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
;;  (bind ([<id> <exp>]) <exp>) -- bind in the monad
;;  (<mnid> <exp> ...)   -- call to a function that doesn't return something in the monad
;;  (<id> <exp> ...)     -- call to a function that returns        something in the monad
;;  (<== <exp>)
;;  <id>
;;  <constant>

;; A pat is either:
;;  <id>
;;  (<id> <id> ...)

(still plenty of work to do here)
|#


;; TODO: Something is wrong because the bt_mt case matches everything
;; on the Racket side. Not sure why. Leave it this way for now so
;; the Coq side gets the right code.
(Fixpoint 
 insert #:implicit @A{Set} @i{A} @b{@"@"bin_tree A}
 #:returns @{@"@"bin_tree A}
 (match b 
   [bt_mt => (<== (bt_node i bt_mt bt_mt))]
   [(bt_node j s t) 
    => 
    (bind ([bt (insert j t)])
      (<== (bt_node i bt s)))]))

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