Set Implicit Arguments.
Require Import Arith.Even Arith.Div2 Omega.

Lemma div2_monotone : forall n, (div2 n <= div2 (S n)).
  apply (ind_0_1_SS (fun n => div2 n <= div2 (S n))); 
  [ | | intros n IndHyp; simpl in IndHyp]; 
  simpl; omega.
Qed.

Lemma lt_div2' : forall n, div2 n < S n.
 intros n.

 apply (le_lt_trans (div2 n) (div2 (S n)) (S n));
   [ apply div2_monotone |  apply lt_div2 ] ;
   omega.
Qed.

Hint Resolve lt_div2'.
Hint Resolve lt_div2.
