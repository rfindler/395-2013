#lang at-exp s-exp "tmonad.rkt"

(define-syntax (match* stx)
  (syntax-parse stx))

(Fixpoint
 rbt_balance #:implicit @A{Set}
 @tl{CTree A} @tc{Color} @tv{A} @tr{CTree A}
 #:returns @{CTree A}
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

(Fixpoint
 rbt_insert_inner #:implicit @A{Set}
 @A_cmp{A -> A -> Prop}
 @A_asym{forall x y, A_cmp x y -> ~ A_cmp y x}
 @A_trans{Transitive A A_cmp}
 @A_cmp_dec{forall (x y:A),
            { A_cmp x y } + { A_cmp y x }}
 @A_eq_dec{forall (x y:A), { x = y } + { x <> y }}
 @ct{CTree A} @x{A}
 #:returns @{CTree A}
 (match (ct)
   [(CT_leaf)
    =>
    (<== (CT_node ct RED x ct))]
   [(CT_node l c v r)
    =>
    (match ((A_eq_dec x v))
      [(left _)
       =>
       (<== ct)]
      [(right _)
       =>
       (match ((A_cmp_dec x v))
         [(left _)
          =>
          (bind 
           ((lp (rbt_insert_inner A_cmp A_asym A_trans A_cmp_dec A_eq_dec l x)))
           (bind 
            ((res (rbt_balance lp c x r)))
            (<== res)))]
         [(right _)
          =>
          (bind 
           ((rp (rbt_insert_inner A_cmp A_asym A_trans A_cmp_dec A_eq_dec r x)))
           (bind 
            ((res (rbt_balance l c x rp)))
            (<== res)))])])]))

(Fixpoint
 rbt_blacken #:implicit @A{Set}
 @ct{CTree A}
 #:returns @{CTree A}
 (match (ct)
   [(CT_leaf)
    =>
    (<== ct)]
   [(CT_node l c v r)
    =>    
    (<== (CT_node l BLACK v r))]))

(Fixpoint
 rbt_insert #:implicit @A{Set}
 @A_cmp{A -> A -> Prop}
 @A_asym{forall x y, A_cmp x y -> ~ A_cmp y x}
 @A_trans{Transitive A A_cmp}
 @A_cmp_dec{forall (x y:A),
            { A_cmp x y } + { A_cmp y x }}
 @A_eq_dec{forall (x y:A), { x = y } + { x <> y }}
 @ct{CTree A} @x{A}
 #:returns @{CTree A}
 (bind 
  ((ctp (rbt_insert_inner A_cmp A_asym A_trans A_cmp_dec A_eq_dec ct x)))
  (bind 
   ((res (rbt_blacken ct)))
   (<== res))))
