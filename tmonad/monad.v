Require Import Program.

Definition C (A:Set) (P:A -> nat -> Prop) : Set := {a | exists n, (P a n)}.
Hint Unfold C.

Definition ret (A:Set) (PA:A -> nat -> Prop) (x:A) (PAx:PA x 0) : C A PA.
Proof.
  exists x.
  exists 0.
  apply PAx.
Defined.

Definition bind (A:Set) (B:Set)
           (PA:A -> nat -> Prop) (PAB:A -> B -> nat -> Prop)
           (xm:C A PA) 
           (yf:forall (x:A),
                 C B 
                   (fun y yn => 
                      forall xn, 
                        PA x xn ->
                        PAB x y (xn+yn)))
: C B (PAB (proj1_sig xm)).
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

Definition inc (A:Set) PA (x:C A (fun x xn => PA x (xn+1)))
: C A PA.
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + 1).
  apply Px.
Defined.

Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.
Require Import Program.Syntax.
Require Import Braun.tmonad.braun Braun.tmonad.util Braun.tmonad.same_structure.
Require Import Braun.tmonad.log.

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "++ ; c" := (inc _ _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ (fun _ => _) y (fun x : _ => z) ) (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ (fun _ => _) x y) (at level 55).
Notation "x >> y" := (bind _ _ _ (fun _ => _) x (fun _ => y)) (at level 30, right associativity).

Notation "{ x !:! A !<! c !>!  P  }" := (C A (fun (x:A) (c:nat) => P)) (at level 55).

Program Fixpoint insert {A:Set} (i:A) (b:@bin_tree A)
: { b' !:! (@bin_tree A) !<! c !>!
       (forall n,
          Braun b n ->
          (Braun b' (S n) /\
           c = fl_log n + 1)) } :=
  match b with
    | bt_mt =>
      (++ ; (<== (bt_node i bt_mt bt_mt)))
    | bt_node j s t =>
      (st <- (insert j t) ;
       (++ ; (<== (bt_node i st s))))
  end.

Obligations.

Next Obligation.
  rename H into B.

  invclr B.
  split; auto.
  replace 1 with (0 + 0 + 1); try omega.
  eapply B_node; auto; try omega.
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
  rename H0 into B.

  invclr B.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.

  apply IH in Bt.
  destruct Bt as [Bst EQ].
  subst xn.
  replace (fl_log t_size + 1) with (S (fl_log t_size)); try omega.
  rewrite fl_log_cl_log_relationship.
  replace (fl_log (s_size + t_size + 1) + 1) with (S (fl_log (s_size + t_size + 1)));
    try omega.
  rewrite fl_log_cl_log_relationship.
  replace (S (s_size + t_size + 1)) with ((S t_size) + s_size + 1); try omega.

  split.
  eapply B_node; auto; try omega.
  apply braun_invariant_implies_cl_log_property.
  replace (S t_size) with (t_size + 1); try omega.
Qed.

Recursive Extraction insert.
