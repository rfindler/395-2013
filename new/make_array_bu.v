Require Import braun log insert util index list_util sequence.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

(* COMMENT: Okasaki's algorithm is wrong or at least ill-defined,
because it (a) relies on in-order matching and assumes that k is not
0, because when it is, the second case infinite loops. *)

Inductive RowsR : nat -> list A -> list (nat * list A) -> nat -> Prop :=
| RR_mt :
    forall k,
      RowsR k nil nil 0
| RR_cons :
    forall k x xs more more_time,
      RowsR (2 * (S k)) (skipn (S k) (x :: xs)) more more_time ->
      RowsR (S k) (x :: xs) (((S k), firstn (S k) (x::xs)) :: more) (more_time + 1).
Hint Constructors RowsR.

Lemma skipn_length :
  forall k (xs:list A),
    length xs - k = length (skipn k xs).
Proof.
  induction k as [|k]; intros xs; simpl.
  omega.
  destruct xs as [|x xs]. 
  simpl. omega.
  simpl. rewrite IHk. auto.
Qed.
Hint Rewrite skipn_length.

(* COMMENT: We incorporate k != 0 into this proof. *)

Theorem rows :
  forall k xs,
    { o | exists t, RowsR (S k) xs o t }.
Proof.
  intros k xs. generalize k. clear k.
  remember (length xs) as n.
  generalize n xs Heqn. clear n xs Heqn.

  apply (well_founded_induction_type
           lt_wf
           (fun n => forall xs, 
                       n = length xs -> 
                       forall k,
                         { o | exists t, RowsR (S k) xs o t })).
  
  intros n IH xs Heqn k.
  destruct xs as [|x xs]. eauto.
  remember (n - (S k)) as y.
  cut (y < n). intros LT.
  remember (skipn (S k) (x :: xs)) as next.
  cut (y = length next). intros EQ.
  edestruct (IH y LT next EQ (pred (2 * (S k)))) as [more IHn].
  exists (((S k), firstn (S k) (x::xs)) :: more).
  destruct IHn as [more_time IHn].
  subst.
  exists (more_time + 1).
  eapply RR_cons.
  replace (S (pred (2 * S k))) with (2 * S k) in *.
  auto.
  omega.

  subst. apply skipn_length.

  clear IH. subst y.
  simpl in *.
  destruct n as [|n]; omega.
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
  simpl in IHRR.
  replace (more_time+1) with (S more_time); try omega.
Qed.

(* XXX keep going! *)
