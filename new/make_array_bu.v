Require Import braun log insert util index list_util sequence.
Require Import Arith Arith.Even Arith.Div2 List NPeano NPow.
Require Import Program.
Require Import Omega.

Inductive RowsR : nat -> list A -> list (nat * list A) -> nat -> Prop :=
| RR_mt :
    forall k,
      RowsR k nil nil 0
| RR_cons :
    forall k x xs more mt,
      RowsR (S k) (skipn (2^k) (x :: xs)) more mt ->
      RowsR k (x :: xs) ((2^k, firstn (2^k) (x::xs)) :: more) (mt + 1).
Hint Constructors RowsR.

Theorem rows :
  forall k xs,
    { o | exists t, RowsR k xs o t }.
Proof.
  intros k xs. generalize k. clear k.
  remember (length xs) as n.
  generalize n xs Heqn. clear n xs Heqn.

  apply (well_founded_induction_type
           lt_wf
           (fun n => forall xs, 
                       n = length xs -> 
                       forall k,
                         { o | exists t, RowsR k xs o t })).
  
  intros n IH xs Heqn k.
  destruct xs as [|x xs]. eauto.
  remember (n - 2^k) as y.
  cut (y < n). intros LT.
  remember (skipn (2^k) (x :: xs)) as next.
  cut (y = length next). intros EQ.
  edestruct (IH y LT next EQ (S k)) as [more IHn].
  exists ((2^k, firstn (2^k) (x::xs)) :: more).
  destruct IHn as [more_time IHn].
  subst.
  exists (more_time + 1).
  eapply RR_cons.
  auto.

  subst. apply skipn_length.

  clear IH. subst y.
  simpl in *.
  destruct n as [|n]; try omega.
  clear Heqn x xs.
  auto.
Qed.
Hint Resolve rows.

(* COMMENT: Trying to bound or be exact on k fails *)

Theorem RowsR_bound_xs :
  forall k xs o t,
    RowsR k xs o t ->
    t <= (length xs).
Proof.
  intros k xs ot t RR.
  induction RR; simpl.
  omega.
  rewrite <- skipn_length in IHRR.
  replace (length (x :: xs)) with (S (length xs)) in *; try auto.
  replace (mt+1) with (S mt); try omega.
  apply le_n_S.
  eapply le_trans; eauto.
Qed.

(* XXX keep going! *)
