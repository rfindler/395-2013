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

  Lemma double_div2 : forall n, div2 (n + n) = n.
    induction n.
    compute; reflexivity.
    replace (S n + S n) with (S (S (n + n))); [|omega].
    unfold div2; fold div2.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma odd_div2 : (forall n, div2 (S (n + n)) = n).
    induction n.
    compute; reflexivity.
    replace (S (S n + S n)) with (S (S (S n + n))) ; [|omega].
    unfold div2 at 1.
    fold div2.
    replace (S n + n) with (S (n + n)) ; [|omega].
    rewrite IHn.
    reflexivity.
  Qed.

Lemma double_is_even: forall n, even (n+n).
  induction n.
  intuition.
  simpl.
  rewrite plus_comm.
  simpl.
  constructor.
  constructor.
  assumption.
Qed.

Lemma odd_not_even : forall n, even (n+n+1) -> False.
  intros n EN.
  inversion EN; intuition.
  rewrite plus_comm in H.
  inversion H.
  assert (even n0); [subst; apply double_is_even|].
  apply (not_even_and_odd n0); assumption.
Qed.

Lemma even_not_odd : forall n, odd(n+n) -> False.
  induction n.
  intros.
  inversion H.
  simpl.
  rewrite plus_comm.
  simpl.
  intros.
  inversion H.
  inversion H1.
  intuition.
Qed.

Lemma div2_with_odd_input: forall n, div2 (S (n+n)) = n.
  induction n.
  simpl. reflexivity.
  simpl.
  rewrite plus_comm.
  unfold plus.
  fold plus.
  rewrite IHn.
  reflexivity.
Qed.
