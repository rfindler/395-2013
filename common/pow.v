Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax List.
Require Import Braun.common.util.

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
  
