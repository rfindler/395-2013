Require Import Braun.tmonad.monad Braun.logical.index Braun.tmonad.insert.
Require Import Braun.common.braun Braun.common.util Braun.common.big_oh.
Require Import Braun.logical.sequence.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf.

Definition copy_insert_time (n:nat) := 3.

Definition copy_insert_result (A:Set) (x:A) (n:nat) (b:@bin_tree A) (c:nat):=
  Braun b n /\ 
  (forall i y, IndexR b i y -> y = x) /\
  c = copy_insert_time (n).

Load "copy_insert_gen.v".

Next Obligation.
  unfold copy_insert_result.
  repeat constructor; auto.
  
  intros i y IR.
  inversion IR.
Qed.

Next Obligation.
  clear am H2.
  rename H1 into CIR.
  rename H into EVENNPRIME.

  inversion CIR as [BRAUNT [HIR TIME]].

  unfold copy_insert_result.
  repeat split.

  (* braun *)
  assert (S n' = div2 n' + div2 n' + 1) as QQ.
  replace (div2 n' + div2 n') with n'; try omega.
  apply even_double; auto.
  rewrite QQ; clear QQ.
  constructor; auto; try omega.

  (* correct *)
  intros i y IR.
  invclr IR; auto.
  remember (HIR i0 y H4).
  auto.

  remember (HIR i0 y H4).
  auto.

  (* running time *)
  admit.
Qed. 

Next Obligation.
  clear am0 H3.
  clear am H4.
  clear copy_insert.
  rename H1 into IR.
  rename H2 into CIR.

  destruct CIR as [BT [INDEX TIME]].

  unfold insert_result in IR.
  remember (IR (div2 n') BT) as IRN.
  clear IR HeqIRN.
  destruct IRN as [BRAUNS [SEQ INSERT_TIME]].

  repeat split.

  (* braun *)
  replace (S n') with (S (div2 n') + (div2 n') + 1).
  constructor; auto; try omega.
  replace (S (div2 n') + div2 n') with (S ((div2 n')+(div2 n'))); try omega.
  replace (div2 n' + div2 n') with (double (div2 n')); auto.
  rewrite <- (odd_double n'); auto; try omega.

  (* correctness *)
  intros i y IR.
  invclr IR; auto.
  admit. (* the case when we called insert *)
  remember (INDEX i0 y H5); auto.

  (* running time *)
  admit.
Qed.
