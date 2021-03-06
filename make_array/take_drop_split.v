Require Import Braun.monad.monad Braun.common.util Braun.common.le_util.
Require Import Braun.common.big_oh.
Require Import Arith Arith.Le Arith.Lt Peano Arith.Min.
Require Import Coq.Arith.Compare_dec.
Require Import Program.Wf Init.Wf.

Include WfExtensionality.

Definition take_time n len := 
  if le_lt_dec len n 
  then 10 * len + 3
  else 10 * n + 5.

Definition take_result (A:Set) n (xs:list A) (res:list A) c := 
  c = take_time n (length xs) /\
  ((length xs) < n -> length res = (length xs)) /\
  (n <= (length xs)  -> length res = n).

Load "take_gen.v".

Next Obligation.
Proof.
  unfold take_result.
  simpl.
  split; [|split;omega].
  unfold take_time.
  dispatch_if REL REL'.
  omega.
  simpl in REL'.
  inversion REL'.
Qed.

Next Obligation.
Proof.
  unfold take_result.
  simpl.
  split.
  unfold take_time.
  dispatch_if REL REL'.
  inversion REL.
  omega.
  split; intros; omega.
Qed.

Next Obligation.
Proof.
  clear am H1.
  rename H0 into RC.

  unfold take_result in *.
  unfold take_time in *.
  destruct RC as [ANeq [SHORT LONG]].

  split.

  subst an.
  dispatch_if COND1 COND1'; dispatch_if COND2 COND2'.
  simpl; omega.
  simpl in COND2'; omega.
  simpl in COND2.
  apply le_S_n in COND2.
  omega.
  omega.

  simpl.

  split; intros LT; omega.
Qed.

Lemma take_linear : forall len, big_oh (fun n => take_time n len) (fun n => n).
Proof.
  intros len.
  exists 1.
  exists 15.
  intros n LT.
  destruct n; intuition.
  clear LT.
  unfold take_time.
  dispatch_if COND COND'; omega.
Qed.

Definition drop_time n len :=
  if le_lt_dec n len
  then 8 * n + 3
  else 8 * len + 5.

Definition drop_result (A:Set) n (xs:list A) (res:list A) c := 
  c = drop_time n (length xs) /\
  ((length xs) < n -> length res = 0) /\
  (n <= (length xs)  -> length res = (length xs) - n).

Load "drop_gen.v".

Next Obligation.
Proof.
  unfold drop_result.
  split.
  unfold drop_time.
  dispatch_if COND COND'; omega.

  split; intros REL.
  inversion REL.
  omega.
Qed.

Next Obligation.
Proof.
  unfold drop_result.
  split.
  simpl.
  unfold drop_time.
  dispatch_if COND COND'; omega.

  split; intros REL.
  simpl.
  omega.
  simpl in REL.
  inversion REL.
Qed.

Next Obligation.
Proof.
  clear am H1.
  rename H0 into RC.

  unfold drop_result in *.
  destruct RC as [ANEQ [SHORT LONG]].

  split.
  subst an.
  simpl.
  unfold drop_time.
  dispatch_if COND COND'; dispatch_if COND2 COND2'; omega.

  split; intros REL.
  simpl in REL.
  apply lt_S_n in REL.
  apply SHORT in REL.
  omega.
  
  simpl in REL.
  apply le_S_n in REL.
  apply LONG in REL.
  simpl; omega.
Qed.

Lemma drop_linear : forall len, big_oh (fun n => drop_time n len) (fun n => n).
Proof.
  intros len.
  exists 1.
  exists 11.
  intros n LT.
  destruct n; intuition.
  clear LT.
  unfold drop_time.
  dispatch_if COND COND'; omega.
Qed.

Definition split_time len k := 
  take_time k len + drop_time k len + 9.

Definition split_result (A:Set) (k:nat) (xs:list A) (res:list A * list A) c :=
  c = split_time (length xs) k /\
  ((length xs) < k -> length (fst res) = (length xs) /\ length (snd res) = 0) /\
  (k <= (length xs) -> 
   length (fst res) = k /\
   length (snd res) = (length xs) - k).

Load "split_gen.v".

Next Obligation.
Proof.
  clear H3 am H2 am0.
  rename H0 into DR.
  rename H1 into TR.

  unfold take_result in *.
  unfold drop_result in *.
  unfold split_result.
  unfold split_time.

  split.
  omega.
  simpl.
  destruct TR. destruct DR.
  split; intros; split; intuition.
Qed.

Lemma split_time_linear : forall len, big_oh (fun n => split_time len n) (fun n => n).
Proof.
  intros len.
  unfold split_time.
  apply big_oh_plus.
  apply big_oh_plus.
  apply take_linear.
  apply drop_linear.
  exists 1.
  exists 10.
  intros; omega.
Qed.

Definition pad_drop_time k := k * 11 + 3.
Hint Unfold pad_drop_time.

Definition pad_drop_result (A:Set) k (xs : list A) (x:A) (res : list A) c :=
  c = pad_drop_time k /\ length res = k.
Hint Unfold pad_drop_result.

Load "pad_drop_gen.v".

Next Obligation.
Proof.
  clear am H1.
  rename H0 into PDRnil.

  unfold pad_drop_result in *.
  unfold pad_drop_time in *.
  destruct PDRnil as [ANeq LReq].
  split; simpl; omega.
Qed.

Next Obligation.
Proof.
  clear am H1.
  rename H0 into PDRrst.
  unfold pad_drop_result in *.
  unfold pad_drop_time in *.
  destruct PDRrst.
  split; auto; simpl; omega.
Qed.

Lemma pad_drop_linear : big_oh pad_drop_time (fun n => n).
Proof.
  apply big_oh_plus; auto.
Qed.
