#lang at-exp s-exp tmonad
(provide rbt_balance)

;; xxx
#;
(define-syntax (match* stx)
  (syntax-parse stx))

(Fixpoint
 rbt_balance #:implicit @A{Set}
 @tl{CTree A} @tc{Color} @tv{A} @tr{CTree A}
 #:returns @{CTree A}
 (<== tl)
 #;
 (match* (tc tl tv tr)
   [((== BLACK) (T:C2 (== RED) (T:C2 (== RED) a xK xV b) yK yV c) zK zV d)
    (T:C2 RED (T:C2 BLACK a xK xV b) yK yV (T:C2 BLACK c zK zV d))]
   [((== BLACK) (T:C2 (== RED) a xK xV (T:C2 (== RED) b yK yV c)) zK zV d)
    (T:C2 RED (T:C2 BLACK a xK xV b) yK yV (T:C2 BLACK c zK zV d))]
   [((== BLACK) a xK xV (T:C2 (== RED) (T:C2 (== RED) b yK yV c) zK zV d))
    (T:C2 RED (T:C2 BLACK a xK xV b) yK yV (T:C2 BLACK c zK zV d))]
   [((== BLACK) a xK xV (T:C2 (== RED) b yK yV (T:C2 (== RED) c zK zV d)))
    (T:C2 RED (T:C2 BLACK a xK xV b) yK yV (T:C2 BLACK c zK zV d))]
   [(c a xK xV b)
    (T:C2 c a xK xV b)]))
