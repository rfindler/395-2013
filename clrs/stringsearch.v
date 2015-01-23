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

Definition IsSubstringAt (w:String) (s:String) (n:nat) : Prop :=
  exists lw ls pre post,
    StringAsList w lw /\
    StringAsList s ls /\
    length pre = n /\
        ls = pre ++ lw ++ post.
Hint Unfold IsSubstringAt.

Program Fixpoint naive_search (w:String) (s:String) {measure (string_len s)} :
  {! mn !:! Exc nat !<! c !>!
    (forall n,
      mn = value n ->
      IsSubstringAt w s n) /\
    (mn = error ->
      forall n,
        ~ IsSubstringAt w s n) /\
    1 * ((string_len s) - (string_len w)) * (string_len w) + 1
    <= c <=
    2 * ((string_len s) - (string_len w)) * (string_len w) + 2 !}
  :=
  match (string_len w) with
    | O =>
      += 1;
      <== (value 0)
    | S _ =>
      match (string_len s) with
        | O =>
          += 2 ;
          <== error
        | S _ =>
          match (beq_nat (string_ref w 0) (string_ref s 0)) with
            | true =>
              res <- naive_search (string_tail w) (string_tail s) ;
              match res with
                | value n =>
                  += 4 ;
                  <== (value (S n))
                | error =>
                  res <- naive_search w (string_tail s) ;
                  match res with
                    | value n =>
                      += 5 ;
                      <== (value (S n))
                    | error =>
                      += 5 ;
                      <== error
                  end
              end
            | false =>
              res <- naive_search w (string_tail s) ;
              match res with
                | value n =>
                  += 4 ;
                  <== (value (S n))
                | error =>
                  += 4 ;
                  <== error
              end
          end
      end
  end.

Next Obligation.
  clear naive_search.
  destruct w as [w_len w_fun].
  destruct s as [s_len s_fun].
  simpl in *. subst w_len.
  split.

  intros n EQ.
  inversion EQ. clear EQ H0 n.
  unfold IsSubstringAt.
  exists (@nil nat).
  destruct (StringAsList_dec (s_len, s_fun)) as [ls SALs].
  exists ls.
  exists (@nil nat).
  exists ls. simpl.
  split; auto.
  split; auto.
  simpl. intros. omega.
 
  split.
  intros EQ. inversion EQ.

  rewrite plus_0_r.
  rewrite <- minus_n_O.
  rewrite mult_0_r.
  rewrite mult_0_r.
  simpl. omega.
Qed.

Next Obligation.
  clear naive_search.
  destruct w as [w_len w_fun].
  destruct s as [s_len s_fun].
  simpl in *. subst w_len s_len.
  rename wildcard' into w_len.
  split; [|split].

  intros n EQ. inversion EQ.

  intros _ n ISA.
  unfold IsSubstringAt in ISA.
  destruct ISA as [lw [ls [pre [post [SALw [SALs [EQn EQls]]]]]]].
  subst n ls.
  destruct SALw as [LENw EQw].
  destruct SALs as [LENs EQs].
  clear EQw EQs.
  simpl in *.
  rewrite app_length in *.
  rewrite app_length in *.
  rewrite <- LENw in LENs.
  omega.

  omega.
Qed.

Obligation Tactic := idtac.
Next Obligation.
  
