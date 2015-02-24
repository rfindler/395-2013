#lang at-exp s-exp tmonad
(provide rbt_balance)

(require (for-syntax racket/base
                     syntax/parse))
(define-syntax (Fixpoint* stx)
  (define (expand-match* stx)
    (syntax-parse stx
      [(_ #:else else:expr
          [{id pat} ... body]
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
 (match* #:else (CT_node tl tc tv tr)
   [{tc BLACK} {tl (CT_node tll tlc tlv tlr)} {tlc RED} 
    {tll (CT_node tlll tllc tllv tllr)} {tllc RED}
    
    (CT_node (CT_node tlll BLACK tllv tllr) RED tlv (CT_node tlr BLACK tv tr))]
   
   [{tc BLACK} {tl (CT_node tll tlc tlv tlr)} {tlc RED} 
    {tlr (CT_node tlrl tlrc tlrv tlrr)} {tlrc RED}
    
    (CT_node (CT_node tll BLACK tlv tlrl) RED tlrv (CT_node tlrr BLACK tv tr))]
   
   [{tc BLACK} {tr (CT_node trl trc trv trr)} {trc RED} 
    {trl (CT_node trll trlc trlv trlr)} {trlc RED}
    
    (CT_node (CT_node tl BLACK tv trll) RED trlv (CT_node trlr BLACK trv trr))]
   
   [{tc BLACK} {tr (CT_node trl trc trv trr)} {trc RED} 
    {trr (CT_node trrl trrc trrv trrr)} {trrc RED}
    
    (CT_node (CT_node tl BLACK tv trl) RED trv (CT_node trrl BLACK trrv trrr))]))
