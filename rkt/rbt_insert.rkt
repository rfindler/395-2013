#lang at-exp s-exp "tmonad.rkt"

(define-syntax (match* stx)
  (syntax-parse stx))

(Fixpoint
 rbt_balance #:implicit @A{Set}
 @tl{CTree A} @tc{Color} @tv{A} @tr{CTree A}
 #:returns @{CTree A}
 
 (match (tc)
   [(RED) => (<== (CT_node tl tc tv tr))]
   [(BLACK)
    =>
    (match (tl)
      [(CT_leaf) => 
       (match (tr)
         [(CT_leaf) => 
          (<== (CT_node tl tc tv tr))]
         [(CT_node bl bc bv br) =>
          (match (bc)
            [(RED) => 
             (match (bl)
               [(CT_leaf) =>
                (match (br)
                  [(CT_leaf) =>
                   (<== (CT_node tl tc tv tr))]
                  [(CT_node brl brc brv brr) =>
                   (match* (brc)
                     ;; case 4
                     [(RED) =>
                      (<== (CT_node (CT_node tl BLACK tv bl) RED bv 
                                    (CT_node brl BLACK brv brr)))]
                     [(BLACK) =>
                      (<== (CT_node tl tc tv tr))])])]
               [(CT_node bll blc blv blr) =>
                (match* (tr)
                  ;; case 3
                  [((CT_node (CT_node b (== RED) yV c) _ _ _))
                   (<== (CT_node (CT_node tl BLACK tv b) RED yV (CT_node c BLACK bv br)))]
                  ;; case 4
                  [((CT_node _ _ _ (CT_node c (== RED) zV d)))
                   (<== (CT_node (CT_node tl BLACK tv bl) RED bv (CT_node c BLACK zV d)))]
                  [(b)
                   (<== (CT_node tl tc tv tr))])])]
            [(BLACK) =>
             (<== (CT_node tl tc tv tr))])])]
      [(CT_node al ac av ar)
       =>       
       (match* (tl tv tr)
         ;; case 1
         [((CT_node (CT_node a (== RED) xV b) (== RED) yV c) zV d)
          (<== (CT_node (CT_node a BLACK xV b) RED  yV (CT_node c BLACK zV d)))]
         ;; case 2
         [((CT_node a (== RED) xV (CT_node b (== RED) yV c)) zV d)
          (<== (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d)))]
         ;; case 3
         [(a xV (CT_node (CT_node b (== RED) yV c) (== RED) zV d))
          (<== (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d)))]
         ;; case 4
         [(a xV (CT_node b (== RED) yV (CT_node c (== RED) zV d)))
          (<== (CT_node (CT_node a BLACK xV b) RED yV (CT_node c BLACK zV d)))]
         [(a xV b)
          (<== (CT_node tl tc tv tr))])])]))

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
