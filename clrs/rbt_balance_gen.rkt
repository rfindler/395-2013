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
 (match* (tc tl tv tr)
   [(BLACK (CT_node (CT_node a RED xK xV b) RED yK yV c) zK zV d)
    (CT_node (CT_node a BLACK xK xV b) RED yK yV (CT_node c BLACK zK zV d))]
   [(BLACK (CT_node a RED xK xV (CT_node b RED yK yV c)) zK zV d)
    (CT_node (CT_node a BLACK xK xV b) RED yK yV (CT_node c BLACK zK zV d))]
   [(BLACK a xK xV (CT_node (CT_node b RED yK yV c) RED zK zV d))
    (CT_node (CT_node a BLACK xK xV b) RED  yK yV (CT_node c BLACK zK zV d))]
   [(BLACK a xK xV (CT_node b RED yK yV (CT_node c RED zK zV d)))
    (CT_node (CT_node a BLACK xK xV b) RED yK yV (CT_node c BLACK zK zV d))]
   [(c a xK xV b)
    (CT_node a c xK xV b)]))
