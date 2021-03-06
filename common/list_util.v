Require Import Braun.common.braun Braun.common.util Braun.common.index.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Program Fixpoint interleave {A:Set} (evens : list A) (odds : list A)
        {measure (length (evens ++ odds))} :=
  match evens with
    | nil => odds
    | (x :: xs) => x :: (interleave odds xs)
  end.
Next Obligation.
Proof.
  simpl.
  rewrite app_length.
  rewrite app_length.
  omega.
Qed.

Lemma interleave_nil1 :
  forall A s,
    @interleave A s nil = s.
Proof.
  induction s as [|x s]; auto.
Qed.
Hint Rewrite interleave_nil1.

Lemma interleave_nil2 :
  forall A t,
    @interleave A nil t = t.
Proof.
  auto.
Qed.
Hint Rewrite interleave_nil2.

Lemma interleave_case2 :
  forall (A:Set) (x:A) ss ts,
    x :: interleave ss ts = interleave (x :: ts) ss.
Proof.
  intros.
  unfold interleave.
  WfExtensionality.unfold_sub 
    interleave_func
    (interleave_func (existT (fun A : Set => (sigT (fun _ : list A => list A))) A (existT (fun _ : list A => list A) (x :: ts) ss))).
  fold interleave_func.
  destruct ts; simpl; reflexivity.
Qed.
Hint Rewrite interleave_case2.

Inductive ListIndexR {A:Set} : list A -> nat -> A -> Prop :=
| LIR_zero :
    forall x xs,
      ListIndexR (x :: xs) 0 x
| LIR_succ :
    forall x xs n y,
      ListIndexR xs n y ->
      ListIndexR (x :: xs) (S n) y.
Hint Constructors ListIndexR.

Theorem ListIndexR_correct :
  forall (A:Set) i xs (x:A),
    nth_error xs i = value x <->
    ListIndexR xs i x.
Proof.
  induction i as [|n]; intros xs y;
  destruct xs as [|x xs]; simpl;
  split; intros H;
  inversion H; subst;
  eauto.

  apply IHn in H1. eauto.
  apply IHn in H4. auto.
Qed.

Lemma ListIndexR_interleave_evens :
  forall (A:Set) ss i y (x:A) ts,
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
  forall (A:Set) ts i y (x:A) ss,
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
  forall A ss ts,
    (length (@interleave A ss ts)) = (length (@interleave A ts ss)).
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
  forall A ss ts,
    (length ss) + (length ts) = (length (@interleave A ss ts)).
Proof.
  induction ss as [|sy ss]; intros ts.

  simpl. auto.

  rewrite <- interleave_case2.
  simpl. rewrite IHss.
  rewrite interleave_length_swap.
  auto.
Qed.
Hint Rewrite interleave_length_split.

Lemma interleave_both:
  forall (A:Set) (e:list A) o,
    length e < S (length (interleave e o))
    /\ length o < S (length (interleave e o)).
Proof.
  intros A. induction e as [|e]; intros o.

  rewrite interleave_nil2.
  simpl. omega.

  rewrite <- interleave_case2.
  simpl.
  rewrite <- interleave_length_swap.
  destruct (IHe o). omega.
Qed.
Hint Resolve interleave_both.

Lemma interleave_evens:
  forall (A:Set) (e:list A) o,
    length e < S (length (interleave e o)).
Proof.
  intros A e o. destruct (interleave_both A e o). auto.
Qed.
Hint Resolve interleave_evens.

Lemma interleave_odds:
  forall (A:Set) (e:list A) o,
    length o < S (length (interleave e o)).
Proof.
  intros A e o. destruct (interleave_both A e o). auto.
Qed.
Hint Resolve interleave_odds.

Lemma interleave_In_swap:
  forall (A:Set) (x:A) s t,
    In x (interleave s t) ->
    In x (interleave t s).
Proof.
  intros A x s. generalize x. clear x.
  induction s as [|sy s]; intros x t IN.

  rewrite interleave_nil2 in IN.
  rewrite interleave_nil1. auto.

  destruct t as [|ty t].
  rewrite interleave_nil1 in IN.
  rewrite interleave_nil2. auto.
  
  rewrite <- interleave_case2 in *.
  rewrite <- interleave_case2 in *.
  simpl in *.
  destruct IN as [EQ|[EQ|IN]]; eauto.
Qed.
Hint Resolve interleave_In_swap.

Lemma interleave_In:
  forall (A:Set) (x:A) s t,
    In x (interleave s t) ->
    In x s \/ In x t.
Proof.
  intros A x s. generalize x. clear x.
  induction s as [|sy s]; intros x t IN.
  right. apply IN.
  rewrite <- interleave_case2 in IN.
  simpl in *.
  destruct IN as [EQ|IN]; eauto.
  apply interleave_In_swap in IN.
  apply IHs in IN.
  destruct IN; eauto.
Qed.
Hint Resolve interleave_In.

Lemma skipn_length :
  forall A k (xs:list A),
    length xs - k = length (skipn k xs).
Proof.
  induction k as [|k]; intros xs; simpl.
  omega.
  destruct xs as [|x xs]. 
  simpl. omega.
  simpl. rewrite IHk. auto.
Qed.
Hint Rewrite skipn_length.
