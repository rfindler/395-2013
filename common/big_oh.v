Require Import Braun.common.log Braun.common.le_util.
Require Import Arith Arith.Mult.

(* big_oh and big_omega definitions based on _Introduction to           *)
(* Algorithms_, 3rd Edition by Thomas H. Cormen, Charles E. Leiserson,  *)
(* Ronald L. Rivest, Clifford Stein                                     *)
(*                                                                      *)
(* but more restrictive in the big_oh case, since we allow only         *)
(* natural number constants. In the big_omega case we effectively       *)
(* allow rational number 'c's, but do it by asking for an explicit      *)
(* numerator and denominator and then multiplying through by the        *)
(* denominator to avoid needing to use rational numbers.                *)

Definition big_oh f g :=
  exists n0 c,
    forall n,
      n0 <= n ->
      f(n) <= c * g(n).

Definition big_omega f g :=
  exists n0 c_num c_den,
    c_num > 0 /\
    forall n,
      n >= n0 ->
      c_num * g(n) <= c_den * f(n).

Definition big_theta f g :=
  big_oh f g /\ big_omega f g.

Lemma big_oh_rev : 
  forall f g,
    big_oh g f ->
    big_omega f g.
Proof.
  intros f g [n0 [m BIGOH_IMP]].
  exists n0.
  exists 1.
  exists m.
  split. auto.
  intros n LT.
  remember (BIGOH_IMP n LT) as LT2; clear HeqLT2.
  clear LT BIGOH_IMP n0.
  rewrite mult_1_l.
  auto.
Qed.

Lemma big_oh_trans :
  forall f g h,
    big_oh f g ->
    big_oh g h ->
    big_oh f h.
Proof.
  intros f g h [FGn [FGm FGP]] [GHn [GHm GHP]].
  exists (FGn+GHn).
  exists (FGm*GHm).
  intros n LE.
  apply (le_trans (f n)
                  (FGm * g n)
                  (FGm * GHm * h n)).
  apply FGP.
  omega.
  rewrite <- mult_assoc.
  apply le_mult_right.
  apply GHP.
  omega.
Qed.

Lemma big_oh_fl_log_plus_1 : big_oh (fun n => (fl_log n + 1)) fl_log.
Proof.
  exists 1.
  exists 2.
  intros n LE.
  destruct n; intuition.
  destruct n; intuition.
  rewrite <- fl_log_div2.
  omega.
Qed.

Lemma big_oh_nlogn_plus_n__nlogn :
  big_oh (fun n : nat => n * fl_log n + n) (fun n : nat => n * fl_log n).
Proof.
  exists 2.
  exists 2.
  intros n L.
  destruct n; intuition.
  destruct n; intuition.
  clear L.
  replace 2 with (1+1); try omega.
  rewrite mult_plus_distr_r.
  unfold mult; fold mult.
  rewrite plus_0_r.

  assert (1 <= fl_log (S (S n))).
  induction n.
  rewrite fl_log_div2'.
  omega.
  apply (le_trans 1 (fl_log (S (S n))) (fl_log (S (S (S n))))); auto.
  apply fl_log_monotone_Sn.

  apply le_plus_right.
  apply (le_trans (S (S n))
                  (1 + 1 + n * fl_log (S (S n)))
                  (fl_log (S (S n)) + (fl_log (S (S n)) + n * fl_log (S (S n))))); try omega.
  apply (le_trans (S (S n))
                  (1 + 1 + n * 1)
                  (1 + 1 + n * fl_log (S (S n)))); try omega.
  rewrite mult_comm.
  apply le_plus_right.
  rewrite mult_comm at 1.
  apply le_mult_right.
  assumption.
Qed.

Lemma big_oh_k___nlogn : 
 forall k, big_oh (fun _ => k) (fun n => n * cl_log n).
Proof.
  intros k.
  exists k.
  exists 1.
  intros n LT.
  rewrite mult_1_l.
  apply (le_trans k n); auto.
  clear k LT.
  destruct n.
  omega.
  replace (S n) with (S n * 1) at 1;[|omega].
  apply mult_le_compat; auto.
  induction n.
  unfold_sub cl_log (cl_log 1).
  omega.
  apply (le_trans 1 (cl_log (S n))); auto.
  apply cl_log_monotone.
  omega.
Qed.

Lemma big_oh_mult :
  forall f g h,
    big_oh f g ->
    big_oh (fun x => (h x) * (f x)) (fun x => (h x) * (g x)).
Proof.
  intros f g n [n0 [m FG]].
  exists n0.
  exists m.
  intros n1 LT.
  apply FG in LT.
  rewrite mult_assoc.
  replace (m * n n1) with (n n1 * m); try (apply mult_comm).
  rewrite <- mult_assoc.
  apply le_mult_right.
  assumption.
Qed.
Hint Resolve big_oh_mult.

Lemma big_oh_plus : 
  forall f g h,
    big_oh f h -> big_oh g h -> big_oh (fun n => f n + g n) h.
Proof.
  intros f g h FG GH.
  destruct FG as [FGn [FGm FG]].
  destruct GH as [GHn [GHm GH]].
  exists (FGn + GHn).
  exists (FGm + GHm).
  intros n LT.
  apply (le_trans (f n + g n)
                  ((FGm * h n) + g n)
                  ((FGm + GHm) * h n)).
  apply le_plus_left.
  apply FG; omega.
  rewrite mult_plus_distr_r.
  apply le_plus_right.
  apply GH; omega.
Qed.
Hint Resolve big_oh_plus.

Lemma big_oh_plus_rev : 
  forall f g h,
    big_oh h f -> big_oh h g -> big_oh h (fun n => f n + g n).
Proof.
  intros f g h HF HG.
  destruct HF as [HFn [HFm HF]].
  destruct HG as [HGn [HGm HG]].
  exists (HFn + HGn).
  exists ((S HFm) * (S HGm)).
  intros n LT.
  repeat (rewrite mult_plus_distr_l).
  assert (h n <= HFm * f n) as LTONE;[apply HF;omega|clear HF].
  assert (h n <= HGm * g n) as LTTWO;[apply HG;omega|clear HG].
  clear LT.
  apply (le_trans (h n) (HFm * f n)); auto.
  replace (S HFm) with (HFm + 1);[|omega].
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_r.
  apply le_plus_trans.
  apply le_plus_trans.
  clear LTONE LTTWO.
  induction HGm.
  rewrite mult_1_r.
  auto.
  apply (le_trans (HFm * f n) (HFm * S HGm * f n)).
  auto.
  apply mult_le_compat; auto.
  apply mult_le_compat; auto.
Qed.

Lemma big_oh_k_linear : forall k, big_oh (fun n => k) (fun n => n).
Proof.
  intros k.
  exists k.
  exists 1.
  intros; omega.
Qed.
Hint Resolve big_oh_k_linear.

Lemma big_oh_n_nlogn:
  big_oh (fun n : nat => n) (fun n : nat => n * cl_log n).
Proof.
  exists 0.
  exists 1.
  intros n _.
  replace (1 * (n * cl_log n)) with (n * cl_log n); [|omega].
  induction n;[omega|].
  apply le_n_S in IHn.
  replace (S n) with (n+1) at 2; [|omega].
  rewrite mult_plus_distr_r.
  apply (le_trans (S n) (S (n * cl_log n))); [omega|].
  clear IHn.
  replace (S (n * cl_log n)) with ((n * cl_log n)+1);[|omega].
  apply plus_le_compat.
  apply mult_le_compat;[omega|].
  apply cl_log_monotone; omega.
  rewrite cl_log_div2'.
  omega.
Qed.

Lemma big_oh_add_k_linear : forall k, big_oh (fun n => n + k) (fun n => n).
Proof.
  intros k.
  exists 1.
  exists (S k).
  intros. 
  destruct n; intuition.
  replace (S k) with (k + 1); [|omega].
  rewrite mult_plus_distr_r.
  replace (k * S n) with (k * (n + 1)).
  rewrite mult_plus_distr_l.
  replace (k*1) with k;[|omega].
  replace (1*S n) with (S n);[|omega].
  apply (le_trans (S n + k)
                  (0 + k + S n)
                  (k*n + k + S n)).
  omega.
  apply le_plus_left.
  apply le_plus_left.
  apply le_0_n.
  replace (n + 1) with (S n); [|omega].
  omega.
Qed.
Hint Resolve big_oh_add_k_linear.

Lemma big_oh_mult_k_right_linear : forall k, big_oh (fun n => n*k) (fun n => n).
Proof.
  intros.
  exists 0.
  exists k.
  intros.
  rewrite mult_comm.
  omega.
Qed.
Hint Resolve big_oh_mult_k_right_linear.

Lemma big_oh_mult_k_left_linear : forall k, big_oh (fun n => k*n) (fun n => n).
Proof.
  intros.
  exists 1.
  exists k.
  intros; omega.
Qed.
Hint Resolve big_oh_mult_k_left_linear.

Lemma big_oh_add_k:
  forall f g k,
    (forall n, 0 < g n) ->
    big_oh f g ->
    big_oh (fun n => f n + k) g.
Proof.
  intros f g k Gpos FG.
  destruct FG as [N [M FG]].
  eexists. exists (M + k).
  intros n LE.
  apply FG in LE.
  rewrite mult_plus_distr_r.
  apply le_add. auto.
  assert (0 < g n) as Gpos'. auto.
  destruct (g n) as [|gn].
  omega.
  rewrite mult_comm. simpl.
  replace k with (k + 0); try omega.
  apply le_add. omega.
  apply le_0_n.
Qed.

Lemma big_oh_add_k_both:
  forall f g k,
    big_oh f g ->
    big_oh (fun n => f n + k) (fun n => g n + k).
Proof.
  intros f g k FG.
  destruct FG as [N [M FG]].
  exists N. exists (S M).
  intros n LE.
  apply FG in LE.
  rewrite mult_plus_distr_l.
  apply le_add. simpl. omega.
  clear FG LE f g N n.
  simpl. 
  replace k with (k + 0); try omega.
  apply le_add. omega.
  apply le_0_n.
Qed.

Lemma big_theta_mult_plus:
  forall x y,
    big_theta (fun n : nat => (S x) * n + y) (fun n : nat => n).
Proof.
  unfold big_theta. split.
  unfold big_oh.
  exists y. exists (S (S x)).
  intros n LE.
  simpl. omega.

  apply big_oh_rev.
  exists 0. exists 1.
  intros n LE. simpl.
  replace n with (n + 0); try omega.
  replace (n + 0 + x * (n + 0) + y + 0) with
    (n + (0 + x * (n + 0) + y + 0)); try omega.
  apply le_add. auto.
  apply le_0_n.
Qed.

Lemma big_oh_eq:
  forall f g,
    (forall n, f n = g n) ->
    big_oh f g.
Proof.
  intros f g EQ.
  exists 0. exists 1.
  intros n LE. rewrite EQ. omega.
Qed.

Lemma big_theta_eq:
  forall f g,
    (forall n, f n = g n) ->
    big_theta f g.
Proof.
  intros f g EQ.
  split. apply big_oh_eq. auto.
  apply big_oh_rev. apply big_oh_eq. auto.
Qed.

Lemma big_omega_rev : 
  forall f g,
    big_omega g f ->
    big_oh f g.
Proof.
  intros f g [n0 [m1 [m2 [GT BIGOM_IMP]]]].
  exists n0.
  exists m2.
  intros n LT.
  remember (BIGOM_IMP n LT) as LT2; clear HeqLT2.
  clear LT BIGOM_IMP n0.
  eapply le_trans; [| apply LT2 ].
  destruct m1 as [|m1]. omega.
  rewrite mult_succ_l.
  apply le_plus_r.
Qed.

Lemma big_theta_trans :
  forall f g h,
    big_theta f g ->
    big_theta g h ->
    big_theta f h.
Proof.
  intros f g h [Ofg Tfg] [Ogh Tgh].
  split. eapply big_oh_trans. apply Ofg. auto.
  apply big_oh_rev. eapply big_oh_trans.
  apply big_omega_rev. apply Tgh.
  apply big_omega_rev. apply Tfg.
Qed.

