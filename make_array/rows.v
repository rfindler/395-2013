Require Import Braun.tmonad.monad Braun.common.util.
Require Import Arith.Le Arith.Lt.
Require Import Coq.Program.Wf.
Require Import Coq.Arith.Compare_dec.

Definition take_result (A:Set) n (xs:list A) (res:list A) c := 
  ((length xs) <= n -> c = 10 * (length xs) + 3) /\
  (n < (length xs)  -> c = 10 * n + 5).

Load "take_gen.v".

Next Obligation.
  unfold take_result.
  split; intros REL.
  simpl.
  omega.
  simpl in REL.
  inversion REL.
Qed.

Next Obligation.
  unfold take_result.
  split; intros REL.
  simpl in REL.
  inversion REL.
  omega.
Qed.

Next Obligation.
  clear am H1.
  rename H0 into RC.

  unfold take_result in *.
  destruct RC as [SHORT LONG].
  
  split; intro AS.

  simpl in AS.
  apply le_S_n in AS.
  apply SHORT in AS.
  simpl.
  omega.

  simpl in AS.
  apply lt_S_n in AS.
  apply LONG in AS.
  omega.
Qed.

Definition drop_result (A:Set) n (xs:list A) (res:list A) c := 
  ((length xs) < n -> c = 8 * (length xs) + 5 /\ length res = 0) /\
  (n <= (length xs)  -> c = 8 * n + 3 /\ length res = (length xs) - n).

Load "drop_gen.v".

Next Obligation.
  unfold drop_result.
  split; intros REL.
  inversion REL.
  omega.
Qed.

Next Obligation.
  unfold drop_result.
  split; intros REL.
  simpl.
  omega.
  simpl in REL.
  inversion REL.
Qed.

Next Obligation.
  clear am H1.
  rename H0 into RC.

  unfold drop_result in *.
  destruct RC as [SHORT LONG].

  split; intros REL.
  
  simpl in REL.
  apply lt_S_n in REL.
  apply SHORT in REL.
  destruct REL as [TIME LENGTH].
  simpl; omega.
  
  simpl in REL.
  apply le_S_n in REL.
  apply LONG in REL.
  simpl; omega.
Qed.

Definition rows_result (A:Set) (k:nat) (xs:list A) (res:list (nat * list A)) c :=
  c+1=c+1.

(* this file was generated automatically from rows.rkt *)
Load "rows_gen.v".

Next Obligation.
Proof.
  unfold rows_result; omega.
Qed.

Next Obligation.
Proof.
  unfold rows_result; omega.
Qed.

Next Obligation.
Proof.
  rename H into DROP_RES.

  unfold drop_result in DROP_RES.

  replace (length (wildcard' :: wildcard'0)) with (S (length wildcard'0)) in *;
    [|simpl;omega].
  remember (length dropped) as l1.
  remember (length wildcard'0) as l2.
  destruct DROP_RES as [L2SMALL L2BIG].

  destruct (le_lt_dec (S n) (S l2)); rename l into LT.
  
  apply L2BIG in LT.
  destruct LT as [AMEQ L1EQ].
  rewrite L1EQ.
  omega.

  apply L2SMALL in LT.
  destruct LT as [AM0EQ L1EQ].
  rewrite L1EQ.
  omega.
Qed.

Next Obligation.
  clear am1 H3.
  clear am H5.
  clear am0 H4.
  unfold rows_result; omega.
Qed.
