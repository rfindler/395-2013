Require Import Braun.tmonad.monad.

Require Import Braun.logical.sequence.
Require Import Braun.logical.list_util.

Require Import Braun.common.braun.
Require Import Braun.common.array.
Require Import Braun.common.util.
Require Import Braun.common.log.

Require Import Braun.common.big_oh Braun.common.le_util Braun.common.util.

Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Definition unravel_time len := 10 * len + 5.

Definition unravel_result (A:Set) (xs:list A) (eo:list A * list A) (c:nat) :=
  let (e, o) := eo in
  xs = interleave e o 
  /\ length o <= length e <= length o + 1
  /\ c = unravel_time (length xs).

Load "unravel_gen.v".

Next Obligation.
Proof.
  rewrite interleave_case2.
  split; auto.
  split.
  omega.
  unfold unravel_time.
  omega.
Qed.

Program Fixpoint make_array_td_time n {measure n} :=
  match n with
    | 0 => 3
    | S n' => 
      10 * n' + 18 + 
      make_array_td_time (div2 (n'+1)) +
      make_array_td_time (div2 n')
  end.

Definition make_array_td_result (A:Set) xs (b:@bin_tree A) c :=
  let n := length xs in
  Braun b n
  /\ c = make_array_td_time n
  /\ SequenceR b xs.

Load "make_array_nlogn2_gen.v".

Next Obligation.
Proof.
  repeat split; auto.
Qed.

Next Obligation.
Proof.
  clear make_array_td.
  rename H into UR.

  unfold unravel_result in UR.
  destruct UR.
  subst xs'.
  simpl. rewrite <- interleave_length_split.
  omega.
Qed.

Next Obligation.
Proof.
  clear make_array_td.
  clear H am0.
  rename H0 into UR.
  unfold unravel_result in UR.
  destruct UR.
  subst xs'.
  simpl. rewrite <- interleave_length_split.
  omega.
Qed.
 
Next Obligation.
Proof.
  clear make_array_td.
  clear am1 H6.
  clear am0 H7.
  rename H0 into MATRevens.
  rename H1 into MATRodds.
  rename l into e. rename l0 into o.

  unfold unravel_result in *.
  unfold make_array_td_result in *.
  
  destruct MATRevens as [BRevens [ANeq SEQevens]].
  destruct MATRodds as [BRodds [AN0eq SEQodds]].

  simpl in *.
  rewrite <- interleave_length_split.
  split; [|split].

  (* braun *)
  replace (S (length e + length o)) with (length e + length o + 1); try omega.
  eauto.

  (* running time *)
  remember (length e) as LE; clear HeqLE.
  remember (length o) as LO; clear HeqLO.
  subst an0 an.
  unfold unravel_time.
  assert (LE = LO \/ LE = LO + 1) as TWOCASES; try omega.
  destruct TWOCASES; subst LE; clear.
  unfold_sub make_array_td_time (make_array_td_time (S (LO+LO))).
  replace (div2 (LO+LO)) with LO; [|rewrite double_div2; reflexivity].
  replace (div2 (LO+LO+1)) with LO.
  omega.
  rewrite <- (div2_with_odd_argument LO) at 1.
  replace (LO+LO+1) with (S (LO+LO)); omega.

  unfold_sub make_array_td_time (make_array_td_time (S (LO+1+LO))).
  replace (LO+1+LO+1) with ((LO+1)+(LO+1)); try omega.
  replace (div2 ((LO+1)+(LO+1))) with (LO+1);[|rewrite double_div2; reflexivity].
  replace (div2 (LO+1+LO)) with LO.
  omega.
  rewrite <- (div2_with_odd_argument LO) at 1.
  replace (LO+1+LO) with (S (LO+LO)); omega.

  (* correctness *)
  eauto.
Qed.

Program Fixpoint make_array_td_time2 n {measure n} :=
  match n with
    | 0 => 1
    | S n' => 
      n' + 
      make_array_td_time2 (div2 (n'+1)) +
      make_array_td_time2 (div2 n')
  end.

Lemma make_array_td_time12 : big_oh make_array_td_time make_array_td_time2.
Proof.
  exists 0.
  exists 28.
  intros n LT;clear LT.
  apply (well_founded_induction
           lt_wf
           (fun n =>  make_array_td_time n <= 28 * make_array_td_time2 n)).
  clear n; intros n IND.
  destruct n.
  compute.
  omega.
  unfold_sub make_array_td_time (make_array_td_time (S n)).
  unfold_sub make_array_td_time2 (make_array_td_time2 (S n)).
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  destruct n.
  compute.
  omega.
  replace (10 * S n) with (10 + 10 * n); [|omega].
  replace (28 * S n) with (28 + 28 * n); [|omega].
  assert (make_array_td_time (div2 (S n + 1)) <=
          28 * make_array_td_time2 (div2 (S n + 1))).
  apply IND; auto.
  assert (make_array_td_time (div2 (S n)) <=
          28 * make_array_td_time2 (div2 (S n))).
  apply IND; auto.
  omega.
Qed.

Lemma make_array_td_time2_mat_time : big_oh make_array_td_time2 mat_time.
Proof.
  exists 1.
  exists 2.
  intros n LT.
  destruct n;intuition.
  clear LT.
  apply (well_founded_induction
           lt_wf
           (fun n => make_array_td_time2 (S n) <= 2 * mat_time (S n))).
  clear n; intros n IND.
  destruct n.
  compute.
  omega.
  rewrite mat_time_Sn.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.

  replace (make_array_td_time2 (S (S n)))
  with ((S n) + make_array_td_time2 (div2 ((S n)+1)) +
        make_array_td_time2 (div2 (S n))).
  replace (S n + 1) with (S (S n)); [|omega].
  destruct n.
  compute.
  omega.
  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|simpl;omega].
  replace (div2 (S (S n))) with (S (div2 n));[|simpl;omega].

  assert (make_array_td_time2 (S (div2 (S n))) <= 2 * mat_time (S (div2 (S n)))).
  apply IND;auto.
  assert (make_array_td_time2 (S (div2 n)) <= 2 * mat_time (S (div2 n))).
  apply IND.
  apply (lt_trans (div2 n) (S n) (S (S n)));auto.
  omega.

  unfold_sub make_array_td_time2 (make_array_td_time2 (S (S n))).
  unfold div2.
  reflexivity.
Qed.  

Theorem make_array_td_nlogn : big_oh make_array_td_time (fun n => n*cl_log n).
Proof.
  apply (big_oh_trans make_array_td_time mat_time (fun n => n*cl_log n)).
  apply (big_oh_trans make_array_td_time make_array_td_time2 mat_time).
  apply make_array_td_time12.
  apply make_array_td_time2_mat_time.
  apply mat_time_nlogn.
Qed.
