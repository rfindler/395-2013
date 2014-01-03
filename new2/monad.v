Require Import Program.

Definition C (A:Set) (P:A -> nat -> Prop) : Set := {a | exists n, (P a n)}.
Hint Unfold C.

Definition ret (A:Set) (PA:A -> nat -> Prop) (x:A) (PAx:PA x 0) : @C A PA.
Proof.
  exists x.
  exists 0.
  apply PAx.
Defined.

Definition bind0 (A:Set) (B:Set) (PA:A -> nat -> Prop) (PB:B -> nat -> Prop)
           (xn:@C A PA) (yf:A -> @C B PB)
           (PBA:forall x xn y yn, (PA x xn) -> (PB y yn) -> (PB y (xn + yn)))
: @C B PB.
Proof.
  destruct xn as [x Px].
  edestruct yf as [y Py].
  apply x.
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply PBA;
  eauto.
Defined.

Definition bind1 (A:Set) (B:Set) (PA:A -> nat -> Prop) (PBi:B -> nat -> Prop) 
           (PB:B -> nat -> Prop)
           (xm:@C A PA) (yf:A -> @C B PBi)
           (PBA:forall x xn y yn, (PA x xn) -> (PBi y yn) -> (PB y (xn + yn)))
: @C B PB.
Proof.
  destruct xm as [x Px].
  edestruct yf as [y Py].
  apply x.
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply PBA.
  apply Px.
  apply Py.
Defined.

Definition bind2 (A:Set) (B:Set)
           (PA:A -> nat -> Prop) (PB:B -> nat -> Prop)
           (xm:@C A PA) 
           (yf:forall (x:A),
                 @C B 
                    (fun y yn => 
                       forall xn, 
                         PA x xn ->
                         PB y (xn+yn)))
: @C B PB.
Proof.
  destruct xm as [x Px].
  edestruct (yf x) as [y Py].
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply Py.
  apply Px.
Defined.

Print bind2.

Definition inc (A:Set) PA (x:@C A (fun x xn => PA x (xn+1)))
: @C A PA.
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + 1).
  apply Px.
Defined.

Recursive Extraction ret bind0 bind1 bind2 inc.

(*
Notation "x >>= y" := (bind x y) (at level 55).
Notation "x >> y" := (bind x (fun _ => y)) (at level 30, right associativity).
Notation "x <- y ; z" := (bind y (fun x : _ => z)) (at level 30, right associativity).
Notation "++ k ; c" := (inc k c) (at level 30, right associativity).
*)

Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.
Require Import Program.Syntax.
Require Import braun util same_structure.
Require Import log.

Definition insert_prop (A:Set) (b:@bin_tree A) :=
  (fun (b':@bin_tree A) (cost:nat) =>
     forall n,
       Braun b n ->
       Braun b' (S n) ->
       cost = fl_log n + 1).
Hint Unfold insert_prop.

Program Fixpoint insert0 {A:Set} (x:A) (b:@bin_tree A)
: @C _ (@insert_prop A b) :=
  match b with
    | bt_mt =>
      (inc _ _
           (ret _ _ (bt_node x bt_mt bt_mt) _))
    | bt_node y s t =>
      (bind0 _ _ _ _ (insert0 y t)
            (fun st =>
               (inc _ _
                    (ret _ _ (bt_node x st s) _)))
            _)
  end.
Obligations.

(* Obligation 2 is clearly false. *)

Admit Obligations.

(* XXX This next one requires a great leap to figure out what the
connection is, but let's try it *)

Program Fixpoint insert1 {A:Set} (i:A) (b:@bin_tree A)
: @C _ (@insert_prop A b) :=
  match b with
    | bt_mt =>
      (inc _ _
           (ret _ _ (bt_node i bt_mt bt_mt) _))
    | bt_node j s t =>
      (@bind1 (@bin_tree A) (@bin_tree A)
              (@insert_prop A t)
              (fun y yn => yn = 1)
              (@insert_prop A (bt_node j s t))
              (insert1 j t)
              (fun st =>
                 (inc _ _
                      (ret _ _ (bt_node i st s) _)))
              _)
  end.

Obligations.

(* Obligation 3 is bad because y is not (bt_node x st s) *)

Admit Obligations.

Program Fixpoint insert2 {A:Set} (i:A) (b:@bin_tree A)
: C _ (insert_prop A b) :=
  match b with
    | bt_mt =>
      (inc _ _
           (ret _ _ (bt_node i bt_mt bt_mt) _))
    | bt_node j s t =>
      (bind2 _ _ _ _ (insert2 j t)
             (fun st =>
                (inc _ _
                     (ret _ _ (bt_node i st s) _))))
  end.

Obligations.

Next Obligation.
  unfold insert_prop.
  intros n B B'.
  invclr B.
  auto.
Qed.

Lemma same_tree_same_size :
  forall A (s:@bin_tree A) n m,
    Braun s n ->
    Braun s m ->
    n = m.
Proof.
  intros A s n m Bn Bm.
  apply (@same_structure_same_size _ s s); eauto.
Qed.
Hint Rewrite same_tree_same_size.

Next Obligation.
  rename H into IH.
  unfold insert_prop.
  intros n B B'.

  invclr B.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.

  invclr B'.
  rename H3 into BP'.
  rename H4 into Bst.
  rename H5 into Bs_again.
  rename H2 into SIZE_EQ.

  replace t_size0 with s_size in *; [|eapply same_tree_same_size; eauto].
  clear Bs_again.
  replace s_size0 with (t_size+1) in *; try omega.
  clear SIZE_EQ.
  replace (t_size + 1) with (S t_size) in Bst; try omega.
  apply IH in Bst; auto.
  subst xn.
  replace (fl_log t_size + 1) with (S (fl_log t_size)); try omega.
  rewrite fl_log_cl_log_relationship.
  replace (fl_log (s_size + t_size + 1) + 1) with (S (fl_log (s_size + t_size + 1)));
    try omega.
  rewrite fl_log_cl_log_relationship.
  replace (S (s_size + t_size + 1)) with ((S t_size) + s_size + 1); try omega.
  apply braun_invariant_implies_cl_log_property.
  replace (S t_size) with (t_size + 1); try omega.
Qed.

Extraction insert2.
