Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax List.
Require Import Braun.common.util Braun.common.log.

Fixpoint pow n m :=
  match m with
    | O =>
      1
    | S m =>
      n * pow n m
  end.

Lemma pow_2_0 : pow 2 0 = 1.
Proof.
  auto.
Qed.
Lemma pow_2_1 : pow 2 1 = 2.
Proof.
  auto.
Qed.
Lemma pow_2_2 : pow 2 2 = 4.
Proof.
  auto.
Qed.

Lemma pow2_monotone:
  forall x y,
    x <= y ->
    pow 2 x <= pow 2 y.
Proof.
  induction x as [|x]; intros y LE.
  simpl. clear LE.
  induction y as [|y]. simpl. auto.
  simpl. omega.
  destruct y as [|y]. omega.
  apply le_S_n in LE.
  apply IHx in LE.
  simpl.  omega.
Qed.
  
Lemma pow_S_non_zero :
  forall m n, 0 < pow (S m) n.
 Proof.
   intros m n.
   induction n.
   simpl.
   omega.
   simpl.
   intuition.
Qed.

Lemma pow2_log :
  forall n, cl_log (pow 2 n) = S n.
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => cl_log (pow 2 n) = (S n))).
  intros n IND.
  destruct n.
  auto.
  replace (pow 2 (S n)) with (2 * (pow 2 n));[|unfold pow;auto].
  remember (pow 2 n) as m.
  destruct m.
  remember (pow_S_non_zero 1 n); intuition.
  replace (2 * S m) with (m + 1 + m + 1);[|omega].
  rewrite <- cl_log_even.
  replace (m+1) with (S m);[|omega].
  replace (cl_log (S m)+1) with (S (cl_log (S m)));[|omega].
  assert (cl_log (S m) = S n);auto.
  rewrite <- (IND n); auto.
Qed.
