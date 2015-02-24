#lang at-exp s-exp tmonad
(provide rbt_balance)

(require (for-syntax racket/base
                     syntax/parse))
(define-syntax (Fixpoint* stx)
  (define (expand-match* stx)
    (syntax-parse stx
      [(_ (expr ...)
          [(pat ...) body]
          ...)
       (syntax/loc stx
         (<== 1))]))
  
  (syntax-parse stx
    [(_ name:id #:implicit iarg:expr arg:expr ... #:returns return:expr
        body:expr)
     (quasisyntax/loc stx
       (Fixpoint name #:implicit iarg arg ... #:returns return
                 #,(expand-match* #'body)))]))

(Fixpoint*
 rbt_balance #:implicit @A{Set}
 @tl{CTree A} @tc{Color} @tv{A} @tr{CTree A}
 #:returns @{CTree A}
 (match* (tl tv tr)
   [{tc BLACK} ((CT_node (CT_node a RED xV b) RED yV c) zV d)
    (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d))]
   [{tc BLACK} ((CT_node a RED xV (CT_node b RED yV c)) zV d)
    (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d))]
   
   [{tc BLACK} (a xV (CT_node (CT_node b RED yV c) RED zV d))
    (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d))]
   [{tc BLACK} (a xV (CT_node b RED yV (CT_node c RED zV d)))
    (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d))]
   
   [(CT_node tl tc tv tr)]))
