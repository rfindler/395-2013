Require Import util log braun.
Require Import Program.Equality.
Require Import Omega.
Require Import Arith Arith.Even Arith.Div2.

Section copy.
  Variable A : Set.
  Variable x : A.

  Inductive Copy2R : nat -> (bin_tree A) * (bin_tree A) -> nat -> Prop :=
    C2R_zero : 
      Copy2R 0 (bt_node x (bt_mt A) (bt_mt A),bt_mt A) 1
  | C2R_even : 
      forall m time s t, 
        Copy2R m (s,t) time ->
        Copy2R (2*m+1) (bt_node x s t, bt_node x t t) (time+2)
  | C2R_odd : 
      forall m time s t, 
        Copy2R m (s,t) time ->
        Copy2R (2*m+2) (bt_node x s s, bt_node x s t) (time+2).
  Hint Constructors Copy2R.

  Inductive CopyR : nat -> bin_tree A -> nat -> Prop :=
    CR : 
      forall n bt1 bt2 time,
        Copy2R n (bt1,bt2) time ->
        CopyR n bt2 time.
  Hint Constructors CopyR.

  Lemma copy2 : 
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
    exists (x0+2).
    replace (S n) with (2*(div2 n)+1).
    eauto.
    rewrite (even_double n) at 2;[|assumption].
    unfold double.
    omega.

    exists (bt_node x s s, bt_node x s t).
    destruct IND2.
    exists (x0+2).
    replace (S n) with (2*(div2 n)+2).
    eauto.
    rewrite (odd_double n) at 2;[|assumption].
    unfold double.
    omega.

  Defined.

  Theorem copy : 
    forall (n:nat), {bt | exists time, CopyR n bt time}.
  Proof.
    intros n.
    destruct (copy2 n) as [[s t] E].
    exists t.
    destruct E.
    eauto.
  Defined.

End copy.

Lemma Copy2_produces_Braun :
  forall A x n bt1 bt2 time, 
    (Copy2R A x n (bt1,bt2) time)
    -> Braun bt1 (n+1) /\ Braun bt2 n.
Proof.
  intros A x n s t time CSR.
  dependent induction CSR; try (inversion IHCSR; clear IHCSR).

  constructor.
  replace (0+1) with (0+0+1);[|omega].
  constructor; [omega|constructor|constructor].
  constructor.

  constructor.

  replace (2*m+1+1) with ((m+1)+m+1);[|omega].
  constructor;[omega|assumption|assumption].

  replace (2*m+1) with (m+m+1);[|omega].
  constructor;[omega|assumption|assumption].

  constructor.

  replace (2*m+2+1) with ((m+1)+(m+1)+1);[|omega].
  constructor;[omega|assumption|assumption].

  replace (2*m+2) with ((m+1)+m+1);[|omega].
  constructor;[omega|assumption|assumption].
Qed.

Lemma Copy_produces_Braun : 
  forall A x n bt time, 
    (CopyR A x n bt time) ->
    Braun bt n.
Proof.
  intros A x n bt time CSR.
  inversion CSR.
  apply Copy2_produces_Braun in H.
  inversion H.
  assumption.
Qed.

Lemma Copy2R_running_time : 
  forall A x n bt1 bt2 time, 
    Copy2R A x n (bt1,bt2) time ->
    time = ((2 * fl_log n) + 1).
Proof.
  intros A x n bt1 bt2 time Copy2.
  dependent induction Copy2.
  compute; reflexivity.

  replace (2*m+1) with (m+m+1); [|omega].
  rewrite fl_log_odd.
  omega.
  
  replace (2*m+2) with ((m+1)+(m+1));[|omega].
  rewrite fl_log_even.
  omega.
Qed.

Lemma CopyR_running_time : 
  forall A x n bt1 time, 
    CopyR A x n bt1 time ->
    time = ((2 * fl_log n) + 1).
  intros.
  inversion H.
  apply Copy2R_running_time in H0.
  assumption.
Qed.
