Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import List.

(* Length and lookup function *)
Definition String := (nat * (nat -> nat))%type.
Hint Unfold String.

Definition string_len (s:String) := fst s.
Hint Unfold string_len.
Definition string_ref (s:String) (n:nat) := (snd s) n.
Hint Unfold string_ref.
Definition string_tail (s:String) : String :=
  ((pred (string_len s)),
    (fun n =>
      (string_ref s (S n)))).
Hint Unfold string_tail.

Definition StringAsList (s:String) (l:list nat) : Prop :=
  string_len s = length l /\
  forall n,
    n < string_len s ->
    nth_error l n = value (string_ref s n).
Hint Unfold StringAsList.

Theorem StringAsList_fun:
  forall s x y,
    StringAsList s x ->
    StringAsList s y ->
    x = y.
Proof.
  intros s x. generalize x s. clear x s.
  induction x as [|xc x];
    intros [s_len s_fun] y [SLx_len SLx_eq] [SLy_len SLy_eq];
      simpl in *.

  subst s_len. destruct y; simpl in *; congruence.

  destruct y as [|yc y]; simpl in *; try congruence.
  destruct s_len as [|s_len]; try congruence.
  replace yc with xc.
  replace y with x.
  auto.
  eapply (IHx (s_len, fun n => s_fun (S n))).
   split.
   simpl. congruence.
   intros n. simpl.
   remember (SLx_eq (S n)) as SLx_eqn. clear HeqSLx_eqn.
   simpl in SLx_eqn.
   intros LE. apply SLx_eqn.
   omega.

   split.
   simpl. congruence.
   intros n. simpl.
   remember (SLy_eq (S n)) as SLy_eqn. clear HeqSLy_eqn.
   simpl in SLy_eqn.
   intros LE. apply SLy_eqn.
   omega.

  remember (SLx_eq 0) as X. clear HeqX.
  remember (SLy_eq 0) as Y. clear HeqY.
  simpl in *.
  assert (0 < S s_len) as LE; try omega.
  apply Y in LE.
  rewrite <- X in LE.
  inversion LE. auto.
  omega.
Qed.

Theorem StringAsList_dec :
  forall s,
    { l | StringAsList s l }.
Proof.
  intros [s_len s_fun]. generalize s_fun. clear s_fun.
  induction s_len as [|s_len]; intros s_fun.

  exists (@nil nat). split. simpl. auto.
  simpl. intros n LE.
  destruct n; try omega.

  destruct (IHs_len (fun n => s_fun (S n))) as [l SAL].
  clear IHs_len.
  exists ((s_fun 0) :: l).
  unfold StringAsList in *.
  simpl in *. destruct SAL as [SALlen SAL].
  subst s_len. split. auto.
  intros n LT.
  destruct n as [|n].
  simpl. auto.
  simpl. apply SAL.
  omega.
Defined.

Definition IsSubstringAtFrom (w:String) (wn:nat) (s:String) (n:nat) : Prop :=
  wn <= string_len w /\
  n + wn <= string_len s /\
  (forall i,
    i < wn ->
    string_ref w i = string_ref s (n + i)).
Hint Unfold IsSubstringAtFrom.

Program Fixpoint naive_search_loop (w:String) (s:String)
  (wn:nat) (sn:nat)
  (ITER_OK:IsSubstringAtFrom w wn s (sn - wn))
  (ITER_FAIL:forall n,
    n <= (sn - (string_len w)) ->
    ~ IsSubstringAtFrom w (string_len w) s n)
  {measure (sn - wn)} :
  {! mn !:! Exc nat !<! c !>!
    (forall n,
      mn = value n ->
      IsSubstringAtFrom w (string_len w) s n) /\
    (mn = error ->
      forall n,
        n <= string_len s - (string_len w) ->
        ~ IsSubstringAtFrom w (string_len w) s n) /\
    0 <= c !}
  :=
  match (beq_nat wn (string_len w)) with
    | true =>
      += 1;
      <== (value (sn - (string_len w)))
    | false =>
      match (beq_nat sn (string_len s)) with
        | true =>
          += 2 ;
          <== error
        | false =>
          match (beq_nat (string_ref w wn) (string_ref s sn)) with
            | true =>
              res <- naive_search_loop w s (S wn) (S sn) _ _ ;
              += 3 ;
              <== res
            | false =>
              res <- naive_search_loop w s 0 (S sn - wn) _ _ ;
              += 3 ;
              <== res
          end
      end
  end.

Lemma minus_plus:
  forall n m,
    m <= n ->
    n - m + m = n.
Proof.
  intros n m. generalize n. clear n.
  induction m as [|m]; intros n LE.

  omega.
  destruct n as [|n].
  omega.
  simpl.
  rewrite plus_comm. simpl.
  rewrite plus_comm. rewrite IHm.
  auto.
  omega.
Qed.
  
Next Obligation.
  clear naive_search_loop.
  rename Heq_anonymous into EQ.
  apply beq_nat_eq in EQ. subst wn.
  split; [|split; [intros EQ; inversion EQ|]].

  intros n EQ. inversion EQ. subst n. clear EQ.
  auto.

  auto.
Qed.

Next Obligation.
  clear naive_search_loop.
  rename Heq_anonymous into NEQ.
  rename Heq_anonymous0 into EQ.
  apply beq_nat_eq in EQ. subst sn.
  split; [|split].

  intros n EQ. inversion EQ.

  intros _ n LE.
  apply ITER_FAIL.
  auto.

  auto.
Qed.

Obligation Tactic := idtac.
Next Obligation.
  intros w s wn sn ITER_OK ITER_FAIL.
  intros _.
  intros h NEQw. subst h. 
  symmetry in NEQw. apply beq_nat_false in NEQw.
  intros h NEQs. subst h.
  symmetry in NEQs. apply beq_nat_false in NEQs.
  intros h EQ. subst h.
  apply beq_nat_eq in EQ.
  clear ITER_FAIL.
  destruct ITER_OK as [LEw [LEs ITER_OK]].
  split; [|split].
  
  inversion LEw. congruence.
  omega.

  admit.

  intros i LT.
  inversion LT.
  subst i.
  simpl.
  rewrite EQ.
  rewrite minus_plus. auto.
  admit.

  subst m. simpl.
  apply ITER_OK.
  omega.
Qed.

