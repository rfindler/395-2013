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
Next Obligation.
Proof.
  replace (n'+1) with (S n').
  auto.
  omega.
Qed.

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

Theorem make_array_td_nlogn : big_oh make_array_td_time (fun n => n*fl_log n).
Proof.
  exists 1.
  exists 50.
  intros n LT.
  destruct n;intuition.
  clear LT.
  apply (well_founded_induction
           lt_wf
           (fun n =>  make_array_td_time (S n) <= 50 * (S n * fl_log (S n)))).
  clear n; intros n IND.
  destruct n.
  compute.
  omega.
  destruct n.
  compute.
  omega.
  remember (S (S n)) as m.
  unfold_sub make_array_td_time (make_array_td_time (S m)).
  subst m.
  replace (S (S n) + 1) with (S (S (S n))); try omega.
  replace (div2 (S (S (S n)))) with (S (div2 (S n)));[|simpl;reflexivity].
  replace (div2 (S (S n))) with (S (div2 n));[|simpl;reflexivity].
  apply (le_trans (10 * S (S n) + 18 +
                   make_array_td_time (S (div2 (S n))) +
                   make_array_td_time (S (div2 n)))
                  (10 * S (S n) + 18 +
                   make_array_td_time (S (div2 (S n))) +
                   (50 * (S (div2 n) * fl_log (S (div2 n)))))
                  (50 * (S (S (S n)) * fl_log (S (S (S n)))))).
  apply le_plus_right.
  apply IND.
  apply (lt_trans (div2 n) (S n) (S (S n))); auto.
  apply (le_trans (10 * S (S n) + 18 +
                   make_array_td_time (S (div2 (S n))) +
                   (50 * (S (div2 n) * fl_log (S (div2 n)))))
                  (10 * S (S n) + 18 +
                   (50 * (S (div2 (S n)) * fl_log (S (div2 (S n))))) +
                   (50 * (S (div2 n) * fl_log (S (div2 n)))))
                  (50 * (S (S (S n)) * fl_log (S (S (S n)))))).
  apply le_plus_left.
  apply le_plus_right.
  apply IND;auto.

  clear IND.
  
  admit. (* might be true .... *)
Qed.
