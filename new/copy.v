Require Import util log braun.
Require Import Omega.
Require Import Arith Arith.Even Arith.Div2.

Section copy.
  Variable A : Set.
  Variable x : A.

  Inductive Copy2R : nat -> (bin_tree A) * (bin_tree A) -> nat -> Prop :=
    C2R_zero : 
      Copy2R 0 (bt_mt A, bt_node x (bt_mt A) (bt_mt A)) 1
  | C2R_even : 
      forall n' time s t, 
        even n' ->
        Copy2R (div2 n') (s,t) time ->
        Copy2R (S n') (bt_node x s t, bt_node x t t) (time+2)
  | C2R_odd : 
      forall n' time s t, 
        odd n' ->
        Copy2R (div2 n') (s,t) time ->
        Copy2R (S n') (bt_node x s s, bt_node x s t) (time+2).
  Hint Constructors Copy2R.

  Inductive CopyR : nat -> bin_tree A -> nat -> Prop :=
    CR : 
      forall n bt1 bt2 time,
        Copy2R n (bt1,bt2) time ->
        CopyR n bt1 time.
  Hint Constructors CopyR.

  Theorem copy2 : 
    forall (n:nat),
      {pr | exists time, Copy2R n pr time}.
  Proof.
    apply (well_founded_induction_type
             lt_wf
             (fun n => {pr | exists time, Copy2R n pr time})).
    intros n IND.
    destruct n.
    eauto.

    destruct (IND (div2 n)) as [PR IND2];[auto|].
    clear IND; destruct PR as [s t].
    destruct (even_odd_dec n).

    exists (bt_node x s t, bt_node x t t).
    destruct IND2.
    eauto.

    exists (bt_node x s s, bt_node x s t).
    destruct IND2.
    eauto.
  Defined.

  Theorem copy : 
    forall (n:nat), {bt | exists time, CopyR n bt time}.
  Proof.
    intros n.
    destruct (copy2 n) as [[s t] E].
    exists s.
    destruct E.
    eauto.
  Defined.

End copy.
