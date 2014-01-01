Require Import braun util index.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Program Fixpoint interleave (evens : list A) (odds : list A)
        {measure (length (evens ++ odds))} :=
  match evens with
    | nil => odds
    | (x :: xs) => x :: (interleave odds xs)
  end.
Next Obligation.
  simpl.
  rewrite app_length.
  rewrite app_length.
  omega.
Qed.

Lemma interleave_case2 :
  forall x ss ts,
    x :: interleave ss ts = interleave (x :: ts) ss.
Proof.
  intros.
  unfold interleave.
  WfExtensionality.unfold_sub 
    interleave_func
    (interleave_func (existT (fun _ : list A => list A) (x :: ts) ss)).
  fold interleave_func.
  destruct ts; simpl; reflexivity.
Qed.
Hint Rewrite interleave_case2.

Inductive ListIndexR : list A -> nat -> A -> Prop :=
| LIR_zero :
    forall x xs,
      ListIndexR (x :: xs) 0 x
| LIR_succ :
    forall x xs n y,
      ListIndexR xs n y ->
      ListIndexR (x :: xs) (S n) y.
Hint Constructors ListIndexR.

Theorem ListIndexR_correct :
  forall i xs x,
    nth_error xs i = value x <->
    ListIndexR xs i x.
Proof.
  induction i as [|n]; intros xs y;
  destruct xs as [|x xs]; simpl;
  split; intros H;
  inversion H; clear H; subst;
  eauto.

  apply IHn in H1. eauto.
  apply IHn in H4. auto.
Qed.

Lemma ListIndexR_interleave_evens :
  forall ss i y x ts,
    length ts <= length ss <= (length ts) + 1 ->
    ListIndexR ss i y ->
    ListIndexR (x :: interleave ss ts) (2 * i + 1) y.
Proof.
  induction ss as [|sy ss]; intros i y x ts BP LIR.
  invclr LIR.

  invclr LIR. simpl.
  eapply LIR_succ. eapply LIR_zero.

  rename H3 into LIR.
  destruct ts as [|ty ts].

  simpl in BP. replace ss with (@nil A) in *.
  invclr LIR.
  destruct ss; simpl in *; try omega.
  auto.

  eapply (IHss _ _ ty ts) in LIR.
  replace (2 * S n + 1) with (S (S (2 * n + 1))); try omega.
  eapply LIR_succ.
  rewrite <- interleave_case2.
  rewrite <- interleave_case2.
  eapply LIR_succ.
  apply LIR.
  simpl in BP. omega.
Qed.
Hint Resolve ListIndexR_interleave_evens.

Lemma ListIndexR_interleave_odds :
  forall ts i y x ss,
    length ts <= length ss <= (length ts) + 1 ->
    ListIndexR ts i y ->
    ListIndexR (x :: interleave ss ts) (2 * i + 2) y.
Proof.
  induction ts as [|ty ts]; intros i y x ss BP LIR.
  invclr LIR.

  destruct i as [|i].
  invclr LIR.

  replace (2 * 0 + 2) with (S (S 0)); try omega.
  eapply LIR_succ.
  destruct ss as [|sy ss].
  simpl in BP. omega.
  rewrite <- interleave_case2.
  eapply LIR_succ.
  eapply LIR_zero.

  invclr LIR. rename H3 into LIR.
  replace (2 * (S i) + 2) with (S (S (2 * i + 2))); try omega.
  eapply LIR_succ.
  destruct ss as [|sy ss].
  simpl in BP. omega.
  rewrite <- interleave_case2.
  eapply LIR_succ.
  rewrite <- interleave_case2.
  eapply IHts; eauto.
  simpl in BP.
  omega.
Qed.
Hint Resolve ListIndexR_interleave_odds.

Lemma interleave_length_swap :
  forall ss ts,
    (length (interleave ss ts)) = (length (interleave ts ss)).
Proof.
  induction ss as [|sy ss]; intros ts.

  induction ts as [|ty ts]; simpl; auto.

  rewrite <- interleave_case2.
  simpl.
  destruct ts as [|ty ts].
  auto.
  rewrite <- interleave_case2.
  rewrite <- interleave_case2.
  rewrite <- interleave_case2.
  simpl. rewrite IHss.
  auto.
Qed.
Hint Rewrite interleave_length_swap.

Lemma interleave_length_split :
  forall ss ts,
    (length ss) + (length ts) = (length (interleave ss ts)).
Proof.
  induction ss as [|sy ss]; intros ts.

  simpl. auto.

  rewrite <- interleave_case2.
  simpl. rewrite IHss.
  rewrite interleave_length_swap.
  auto.
Qed.
Hint Rewrite interleave_length_split.
