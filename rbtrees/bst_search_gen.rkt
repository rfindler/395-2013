#lang at-exp s-exp tmonad

(Fixpoint
 bst_search #:implicit @A{Set}
 @A_cmp{A -> A -> Prop}
 @A_asym{forall x y, A_cmp x y -> ~ A_cmp y x}
 @A_trans{Transitive A A_cmp}
 @A_cmp_dec{forall (x y:A),
            { A_cmp x y } + { A_cmp y x }}
 @A_eq_dec{forall (x y:A), { x = y } + { x <> y }}
 @x{A} @ct{CTree A}
 #:returns @{bool}
 (match (ct)
   [(CT_leaf)
    =>
    (<== false)]
   [(CT_node l c v r)
    =>
    (match ((A_eq_dec x v))
      [(left _)
       =>
       (<== true)]
      [(right _)
       =>
       (match ((A_cmp_dec x v))
         [(left _)
          =>
          (bind ((res (bst_search A_cmp A_asym A_trans A_cmp_dec A_eq_dec x l)))
                (<== res))]
         [(right _)
          =>
          (bind ((res (bst_search A_cmp A_asym A_trans A_cmp_dec A_eq_dec x r)))
                (<== res))])])]))
