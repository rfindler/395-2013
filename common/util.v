Set Implicit Arguments.
Require Import Arith.Even Arith.Div2 Omega NPow.

(* I think this is stdlib somewhere *)
Lemma plus_r_inj : 
  forall m n1 n2, 
    n1 = n2 -> m + n1 = m + n2.
Proof.
  intros; omega.
Qed.
Hint Rewrite plus_r_inj.

Lemma div2_monotone : 
  forall n, 
    (div2 n <= div2 (S n)).
Proof.
  apply (ind_0_1_SS (fun n => div2 n <= div2 (S n)));
  [ | | intros n IndHyp; simpl in IndHyp];
  simpl; omega.
Qed.
Hint Resolve div2_monotone.

Lemma lt_div2' :
  forall n, div2 n < S n.
Proof.
  intros n.
  apply (le_lt_trans (div2 n) (div2 (S n)) (S n));
    [ apply div2_monotone |  apply lt_div2 ] ;
    omega.
Qed.
Hint Resolve lt_div2'.

Lemma lt_div2'' :
  forall n, div2 (S n) < S n.
Proof.
  apply (ind_0_1_SS (fun n => div2 (S n) < S n));
  intros; simpl; try simpl in H; omega.
Qed.
Hint Resolve lt_div2''.

Hint Resolve lt_div2.

Lemma lt_div2''' : forall m', div2 (m' - 1) < S m'.
Proof.
  intros.
  apply (le_lt_trans (div2 (m' - 1))
                     (div2 m')
                     (S m')); auto.
  destruct m'; auto.
  replace (S m' - 1) with m';[|omega].
  auto.
Qed.
Hint Resolve lt_div2'''.


Lemma double_div2 : 
  forall n, div2 (n + n) = n.
Proof.
  induction n.
  compute; reflexivity.
  replace (S n + S n) with (S (S (n + n))); [|omega].
  unfold div2; fold div2.
  rewrite IHn.
  reflexivity.
Qed.
Hint Rewrite double_div2.

Lemma div2_with_odd_argument : 
  (forall n, div2 (S (n + n)) = n).
Proof.
  induction n.
  compute; reflexivity.
  replace (S (S n + S n)) with (S (S (S n + n))) ; [|omega].
  unfold div2 at 1.
  fold div2.
  replace (S n + n) with (S (n + n)) ; [|omega].
  rewrite IHn.
  reflexivity.
Qed.
Hint Rewrite div2_with_odd_argument.

Lemma div2_doubled_le_n :
  forall n,
    div2 n + div2 n <= n.
  intros n.
  assert (even n \/ odd n) as H;[apply even_or_odd|destruct H].

  rewrite even_double;[unfold double;constructor|assumption].

  rewrite odd_double;[unfold double;constructor;constructor|assumption].
Qed.

Lemma double_is_even: 
  forall n, even (n+n).
Proof.
  induction n.
  intuition.
  simpl.
  rewrite plus_comm.
  simpl.
  constructor.
  constructor.
  assumption.
Qed.
Hint Resolve double_is_even.

Lemma odd_not_even : 
  forall n, even (n+n+1) -> False.
Proof.
  intros n EN.
  inversion EN; intuition.
  rewrite plus_comm in H.
  inversion H.
  assert (even n0); [subst; apply double_is_even|].
  apply (not_even_and_odd n0); assumption.
Qed.
Hint Resolve odd_not_even.

Lemma even_not_odd : 
  forall n, odd(n+n) -> False.
Proof.
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
Hint Resolve even_not_odd.

Lemma div2_with_odd_input:
  forall n, div2 (S (n+n)) = n.
Proof.
  induction n.
  simpl. reflexivity.
  simpl.
  rewrite plus_comm.
  unfold plus.
  fold plus.
  rewrite IHn.
  reflexivity.
Qed.
Hint Rewrite div2_with_odd_input.

Lemma minus_0r : 
  forall n, n-0=n.
Proof.
  induction n; simpl; reflexivity.
Qed.
Hint Rewrite minus_0r.

Ltac dispatch_if name2 name3 :=
  match goal with
    | [ |- context[if ?X then _ else _] ] =>
      (remember X as junque1 eqn: junque2;
       destruct junque1 as [name2|name3];
       clear junque2)
  end.

Lemma odd_cleanup :
  forall k n,
    odd n -> div2 n + (div2 n) + (1+k) = n + k.
Proof.
  intros n k H.
  apply odd_double in H.
  unfold double in H.
  omega.
Defined.
Hint Rewrite odd_cleanup.

Lemma even_cleanup :
  forall k n,
    even n -> div2 n + (div2 n) + k = n + k.
Proof.
  intros n k H.
  apply even_double in H.
  unfold double in H.
  omega.
Defined.
Hint Rewrite even_cleanup.

Lemma plusone_ne_zero:
  forall n,
    n + 1 <> 0.
Proof.
  intros. omega.
Qed.
Hint Resolve plusone_ne_zero.

Ltac invclr X :=
  inversion X; clear X; subst.

Lemma minus_ltS :
  forall m n,
    m > 0 ->
    S n - m < S n.
Proof.
  induction m as [|m]; simpl; intros n LT; omega.
Qed.
Hint Resolve minus_ltS.

Lemma pow_lt_O :
  forall k,
    NPeano.pow 2 k > 0.
Proof.
  induction k as [|k]; simpl; omega.
Qed.
Hint Resolve pow_lt_O.

Lemma pow_le_S:
  forall n k,
    S n - (NPeano.pow 2 k) <= n.
Proof.
  intros n k.
  remember (NPeano.pow 2 k) as m.
  assert (m > 0); [subst; auto |].
  assert (S n - m < S n); [subst; auto |].
  omega.
Qed.
Hint Resolve pow_le_S.


Lemma braun_invariant_even_size : 
  forall s_size t_size, even (s_size+t_size+1) -> (t_size <= s_size <= t_size+1) -> s_size = t_size+1.
  intros.
  assert (t_size = s_size \/ s_size = t_size + 1) as TWOCASES;[omega|destruct TWOCASES].
  subst.
  apply odd_not_even in H.
  intuition.
  assumption.
Qed.

Lemma braun_invariant_odd_size : 
  forall s_size t_size, odd (s_size+t_size+1) -> (t_size <= s_size <= t_size+1) -> s_size = t_size.
  intros.
  assert (t_size = s_size \/ s_size = t_size + 1) as TWOCASES;[omega|destruct TWOCASES].
  subst; reflexivity.

  subst.
  replace (t_size+1+t_size+1) with ((t_size+1)+(t_size+1)) in H;[|omega].
  apply even_not_odd in H.
  intuition.
Qed.
