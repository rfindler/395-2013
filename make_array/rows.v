Require Import Braun.tmonad.monad Braun.common.util.
Require Import Arith.Le Arith.Lt.

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
  ((length xs) < n -> c = 8 * (length xs) + 5) /\
  (n <= (length xs)  -> c = 8 * n + 3).

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
  reflexivity.
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
  subst an.
  simpl; omega.
  
  simpl in REL.
  apply le_S_n in REL.
  apply LONG in REL.
  omega.
Qed.

