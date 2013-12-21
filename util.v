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

Lemma lt_div2'' : forall n, div2 (S n) < S n.
  apply (ind_0_1_SS (fun n => div2 (S n) < S n)); 
    intros; simpl; try simpl in H; omega.
Qed.

Hint Resolve lt_div2''.
Hint Resolve lt_div2'.
Hint Resolve lt_div2.

Lemma plus_one : forall n, n+1 = S n. 
  intros. rewrite plus_comm. unfold plus. reflexivity.
Qed.

Hint Rewrite plus_one.

Lemma times_two : forall n, 2*n = n+n. 
  intros. unfold mult. rewrite plus_0_r. reflexivity.
Qed.

Hint Rewrite plus_one.
Hint Rewrite times_two.
