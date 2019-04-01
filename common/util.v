Set Implicit Arguments.
Require Import Arith.Even Arith.Div2 Coq.Arith.Min.
Require Import Omega NPow.


(* I think this is stdlib somewhere *)
Lemma plus_r_inj : 
  forall m n1 n2, 
    n1 = n2 -> m + n1 = m + n2.
Proof.
  intros; omega.
Qed.
Hint Rewrite plus_r_inj.

Lemma div2_monotone_Sn : 
  forall n, 
    (div2 n <= div2 (S n)).
Proof.
  apply (ind_0_1_SS (fun n => div2 n <= div2 (S n)));
  [ | | intros n IndHyp; simpl in IndHyp];
  simpl; omega.
Qed.
Hint Resolve div2_monotone_Sn.

Lemma div2_monotone : forall n m, n <= m -> div2 n <= div2 m.
Proof.
  intros n m.
  induction 1; auto.
  apply (le_trans (div2 n) (div2 m) (div2 (S m))); auto.
Qed.

Lemma lt_div2' :
  forall n, div2 n < S n.
Proof.
  intros n.
  apply (le_lt_trans (div2 n) (div2 (S n)) (S n));
    [ apply div2_monotone_Sn |  apply lt_div2 ] ;
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

Lemma lt_div2'''' : forall n, S (div2 n) < S (S (S n)).
Proof.
  intros n.
  apply lt_n_S.
  apply (lt_trans (div2 n) (S n) (S (S n))); auto.
Qed.
Hint Resolve lt_div2''''.

Lemma div2_succ_lt_div2_plus_one : forall n',  div2 (S n') <= div2 n' + 1.
Proof.
  apply (ind_0_1_SS (fun n' =>  div2 (S n') <= div2 n' + 1));auto;try (simpl;omega).
  intros n IND.
  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|auto].
  replace (div2 (S (S n))) with (S (div2 n));[|auto].
  replace (S (div2 n) + 1) with (S (div2 n + 1));[|omega].
  apply le_n_S.
  assumption.
Qed.
Hint Resolve div2_succ_lt_div2_plus_one. 

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

Lemma div2_with_odd_argument: 
  forall n, div2 (S (n + n)) = n.
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
Proof.
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

Lemma div_ceil_floor_sum : forall n, n = div2 n + div2 (n + 1).
Proof.
  apply (ind_0_1_SS (fun n => n = div2 n + div2 (n + 1)));auto.
  intros.
  simpl.
  replace (S (div2 n + S (div2 (n + 1)))) 
  with ((div2 n + div2 (n+1))+2);omega.
Qed.

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

Search even.

Lemma pow_lt_O :
  forall k,
    Nat.pow 2 k > 0.
Proof.
  induction k as [|k]; simpl; omega.
Qed.
Hint Resolve pow_lt_O.

Lemma pow_le_S:
  forall n k,
    S n - (Nat.pow 2 k) <= n.
Proof.
  intros n k.
  remember (Nat.pow 2 k) as m.
  assert (m > 0); [subst; auto |].
  assert (S n - m < S n); [subst; auto |].
  omega.
Qed.
Hint Resolve pow_le_S.


Lemma braun_invariant_even_size : 
  forall s_size t_size, even (s_size+t_size+1) -> (t_size <= s_size <= t_size+1) -> s_size = t_size+1.
Proof.
  intros.
  assert (t_size = s_size \/ s_size = t_size + 1) as TWOCASES;[omega|destruct TWOCASES].
  subst.
  apply odd_not_even in H.
  intuition.
  assumption.
Qed.

Lemma braun_invariant_odd_size : 
  forall s_size t_size, odd (s_size+t_size+1) -> (t_size <= s_size <= t_size+1) -> s_size = t_size.
Proof.
  intros.
  assert (t_size = s_size \/ s_size = t_size + 1) as TWOCASES;[omega|destruct TWOCASES].
  subst; reflexivity.

  subst.
  replace (t_size+1+t_size+1) with ((t_size+1)+(t_size+1)) in H;[|omega].
  apply even_not_odd in H.
  intuition.
Qed.

Lemma plus_succ_r:
  forall n,
    n + 1 = S n.
Proof.
  intros. omega.
Qed.

Lemma min_div2:
  forall L,
    min (div2 L) L = (div2 L).
Proof.
  intros L.
  apply min_l.
  generalize L. clear L.
  apply ind_0_1_SS; simpl.

  auto. auto.
  intros L IH.
  omega.
Qed.

Lemma min_same : forall n, min n n = n.
Proof.
  intros.
  destruct (min_dec n n) as [A|A];rewrite A; auto.
Qed.

Definition double_plus1 n := S (double n).

Definition even_oddb n := if (even_odd_dec n) then true else false.

Lemma move_inside_div2 :
  forall n m, even m -> div2(n+m) = div2(n)+div2(m).
Proof.
  intros n m EVEN.
  generalize dependent n.
  apply (well_founded_ind
           lt_wf
           (fun n => div2(n+m) = div2 n + div2 m)).
  intros n IND.
  destruct n.
  simpl; auto.
  destruct n.
  simpl.
  destruct m.
  simpl; auto.
  rewrite odd_div2; inversion EVEN; auto.
  replace (S (S n) + m) with (S (S (n+m)));auto.
  replace (div2 (S (S (n+m)))) with (S (div2 (n+m)));[|unfold div2;auto].
  simpl div2.
  replace (S (div2 n) + div2 m) with (S (div2 n + div2 m));[|omega].
  assert (div2 (n + m) = div2 n + div2 m);auto.
Qed.

Lemma even_div_product :
  forall n m, 
    even n ->
    div2 (n*m) = (div2 n) * m.
Proof.
  intros n m.
  apply (well_founded_ind
           lt_wf (fun n => even n -> div2 (n*m) = div2 n * m)).
  clear n; intros n IND EVEN.
  destruct n.
  simpl; auto.

  destruct n.
  inversion EVEN as [|A B C]; inversion B.

  destruct n.
  simpl.
  rewrite plus_0_r.
  apply double_div2.

  replace (div2 (S (S (S n)))) with ((div2 (S n))+1);[|unfold div2;omega].
  rewrite mult_plus_distr_r.
  rewrite <- IND;[|auto|inversion EVEN as [|A B C]; inversion B; auto].
  rewrite mult_1_l.
  replace m with (div2(double m)) at 3; [|unfold double; apply double_div2].
  rewrite <- move_inside_div2; [|unfold double;apply double_is_even].
  unfold double.
  replace (S (S (S n))) with (S n + 2);[|omega].
  rewrite mult_plus_distr_r.
  replace (S n * m + 2 * m) with (S n * m + (m+m));[|omega].
  omega.
Qed.

