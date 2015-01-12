Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.

Inductive Fib : nat -> nat -> Prop :=
| F_0 :
  Fib 0 1
| F_1 :
  Fib 1 1
| F_n :
  forall n a b,
    Fib n a ->
    Fib (S n) b  ->
    Fib (S (S n)) (a + b).
Hint Constructors Fib.

Fixpoint fib_rec_time (n:nat) :=
  match n with
    | O =>
      1
    | S n' =>
      match n' with
        | O =>
          2
        | S n'' =>
          (fib_rec_time n'') + (fib_rec_time n') + 2
      end
  end.

Program Fixpoint fib_rec (n:nat) :
  {! res !:! nat !<! c !>!
    Fib n res /\
    c = fib_rec_time n !}
  :=
  match n with
    | O =>
      += 1;
      <== 1
    | S n' =>
      match n' with
        | O =>
          += 2;
          <== 1
        | S n'' =>
          a <- fib_rec n'' ;
          b <- fib_rec n' ;
          += 2 ;
          <== (a + b)
      end
  end.

Next Obligation.
  split. eauto.
  clear a b H6 H1 H4 H0.
  rename n'' into n.
  destruct n as [|n]; simpl; omega.
Qed.

Lemma fib_rec_time_SSSn:
  forall n,
    fib_rec_time (S (S (S n))) =
    2 * fib_rec_time (S n) + fib_rec_time n + 4.
Proof.
  intros n.
  replace (fib_rec_time (S (S (S n)))) with
    ((fib_rec_time (S n)) + (fib_rec_time (S (S n))) + 2); try auto.
  replace (fib_rec_time (S (S n))) with
    ((fib_rec_time n) + (fib_rec_time (S n)) + 2); try auto.
  omega.
Qed.

Lemma fib_rec_monotone:
  forall n,
    fib_rec_time n < fib_rec_time (S n).
Proof.
  induction n as [|[|n]]; simpl; omega.
Qed.

Fixpoint pow n m :=
  match m with
    | O =>
      1
    | S m =>
      n + pow n m
  end.

Lemma fib_rec_time_upper:
  forall n,
    pow 2 n <= fib_rec_time (S n).
Proof.
  induction n as [|[|n]].  
  simpl. auto.
  simpl. auto.
  rewrite fib_rec_time_SSSn.
  replace (fib_rec_time (S (S n))) with
    ((fib_rec_time n) + (fib_rec_time (S n)) + 2) in IHn; try auto.
  remember (fib_rec_time n) as N.
  remember (fib_rec_time (S n)) as SN.
  assert (N < SN) as LT.
  subst N SN.
  apply fib_rec_monotone.
  clear HeqN HeqSN.
  simpl in *.
  omega.
Qed.

Program Fixpoint fib_iter_loop (fuel:nat) (target:nat) (a:nat) (b:nat) :
  {! res !:! nat !<! c !>!
    1 < target ->
    fuel < target ->
    Fib (target - fuel - 1) a ->
    Fib (target - fuel) b ->
    Fib target res /\
    c = fuel + 1 !}
  :=
  match fuel with
    | O =>
      += 1 ;
      <== b
    | S fuel =>
      res <- fib_iter_loop fuel target b (a + b) ;
      += 1 ;
      <== res
  end.

Next Obligation.
  rewrite <- minus_n_O in *. auto.
Qed.

Next Obligation.
 rename fuel0 into fuel.
 clear am H5.
 rename H0 into IH.
 rename H1 into LT.
 rename H2 into LE.
 rename H3 into Fa.
 rename H4 into Fb.
 edestruct IH as [Fab EQan].
 auto. omega.
 replace (target - fuel - 1) with (target - S fuel). auto.
 omega.

 destruct target as [|target].
 omega.
 destruct target as [|target].
 omega.
 destruct fuel as [|fuel].
 simpl in *.
 rewrite <- minus_n_O in *. auto.
 simpl in Fb.
 simpl in Fa.
 replace (S (S target) - S fuel) with (S (target - fuel)); try omega.
 remember (target - fuel) as TF.
 destruct TF as [|TF].
 simpl in *.
 replace fuel with target in *; try omega.

 simpl in Fa.
 rewrite <- minus_n_O in *.
 auto.

 subst an. split. auto.
 omega.
Qed.

Fixpoint fib_iter_time (n:nat) :=
  match n with
    | O =>
      1
    | S n' =>
      match n' with
        | O =>
          2
        | S n'' =>
          n'' + 4
      end
  end.

Program Fixpoint fib_iter (target:nat) :
  {! res !:! nat !<! c !>!
    Fib target res /\
    c = fib_iter_time target !}
  :=  
  match target with
    | O =>
      += 1 ;
      <== 1
    | S target' =>
      match target' with
        | O =>
          += 2 ;
          <== 1
        | S target'' =>
          res <- fib_iter_loop target' target 1 1 ;
          += 2 ;
          <== res
      end
  end.

Next Obligation.
  clear am H1.
  rename H0 into FIL.
  edestruct FIL; [ | | | | split; [ auto | omega ]]; clear FIL.
  omega. omega.
  replace (S (S target'') - S target'' - 1) with 0; try omega.
  auto.
  replace (S (S target'') - S target'') with 1; try omega.
  auto.
Qed.

Theorem fib_iter_is_better:
  forall n,
    fib_iter_time n <= fib_rec_time n.
Proof.
  intros [|n].
  simpl. auto.
  destruct n as [|n].
  simpl. auto.
  destruct n as [|n].
  simpl. auto.
  eapply le_trans; [ | apply fib_rec_time_upper ].
  simpl.

  induction n as [|n].
  simpl. auto.
  simpl pow. omega.
Qed.

Require Import Div2.

Lemma pow2_monotone:
  forall x y,
    x <= y ->
    pow 2 x <= pow 2 y.
Proof.
  induction x as [|x]; intros y LE.
  simpl.
  destruct y as [|y]. simpl. auto.
  simpl. omega.
  destruct y as [|y]. omega.
  apply le_S_n in LE.
  apply IHx in LE.
  simpl.  omega.
Qed.
  
Lemma fib_rec_time_guarantee:
  ~
  (forall n,
    pow 2 (div2 n) <= fib_rec_time n <= pow 2 n).
Proof.
  intros H.
  destruct (H 3) as [Pl Pr].
  simpl in *. omega.
Qed.
