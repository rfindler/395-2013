Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Div2.
Require Import Relations_1.
Require Import Braun.rbtrees.rbtree.

Definition SameMembers {A:Set} (x:CTree A) (y:CTree A) :=
  forall e,
    IsMember e x <-> IsMember e y.

Lemma SameMembers_refl:
  forall A (x:CTree A),
    SameMembers x x.
Proof.
  intros A x e. intuition.
Qed.

Lemma SameMembers_child:
  forall A (l r:CTree A) v c1 c2,
    SameMembers (CT_node A l c1 v r) (CT_node A l c2 v r).
Proof.
  intros. split; intros IM; inversion IM; subst; eauto.
Qed.

Definition SomeRB {A:Set} (ct:CTree A) :=
  exists n, IsRB ct n.

Lemma SomeRB_node_l:
  forall A l c v r,
    SomeRB (CT_node A l c v r) ->
    SomeRB l.
Proof.
  unfold SomeRB.
  intros. destruct H as [n RB].
  inversion RB; subst; eauto.
Qed.

Lemma SomeRB_node_r:
  forall A l c v r,
    SomeRB (CT_node A l c v r) ->
    SomeRB r.
Proof.
  unfold SomeRB.
  intros. destruct H as [n RB].
  inversion RB; subst; eauto.
Qed.

Definition rbt_blacken_worst := 8.
Definition rbt_blacken_best := 3.

Definition rbt_blacken_result (A:Set) (ct:CTree A) (res:CTree A) (c:nat) :=
  (SomeRB ct -> SomeRB res) /\
  (IsColor res BLACK) /\
  (forall A_cmp min max,
    IsBST A_cmp ct min max ->
    IsBST A_cmp res min max) /\
  (SameMembers ct res) /\
  (rbt_blacken_best <= c <= rbt_blacken_worst).

Load "rbt_blacken_gen.v".

Next Obligation.
Proof.
  unfold rbt_blacken_result.
  split. auto.
  split. auto.
  split. intuition.
  split. apply SameMembers_refl.
  unfold rbt_blacken_best, rbt_blacken_worst.
  omega.
Qed.

Next Obligation.
Proof.
  unfold rbt_blacken_result.
  split. intros [n RB].
  apply blacken_okay in RB.
  unfold SomeRB. destruct RB; eauto.
  split. auto.
  split.
   intros A_cmp min max BST.
   inversion BST. subst. eauto.
  split. apply SameMembers_child.
  unfold rbt_blacken_best, rbt_blacken_worst.
  omega.
Qed.

Inductive RBT_Balance (A:Set) : CTree A -> Color -> A -> CTree A -> CTree A -> Prop :=
| RBTB_Case1 :
  forall tlll tllv tllr tlv tlr tv tr,
    RBT_Balance A (CT_node A (CT_node A tlll RED tllv tllr) RED tlv tlr) BLACK tv tr
    (CT_node A 
      (CT_node A tlll BLACK tllv tllr) RED tlv 
      (CT_node A tlr BLACK tv tr))
| RBTB_Case2 :
  forall tll tlv tlrl tlrv tlrr tv tr,
    RBT_Balance A (CT_node A tll RED tlv (CT_node A tlrl RED tlrv tlrr)) BLACK tv tr
    (CT_node A (CT_node A tll BLACK tlv tlrl) RED tlrv 
      (CT_node A tlrr BLACK tv tr))
| RBTB_Case3 :
  forall tl tv trll trlv trlr trv trr,
    RBT_Balance A tl BLACK tv (CT_node A (CT_node A trll RED trlv trlr) RED trv trr)
    (CT_node A (CT_node A tl BLACK tv trll) RED trlv
      (CT_node A trlr BLACK trv trr))
| RBTB_Case4 :
  forall tl tv trl trv trrl trrv trrr,
    RBT_Balance A tl BLACK tv (CT_node A trl RED trv (CT_node A trrl RED trrv trrr))
    (CT_node A (CT_node A tl BLACK tv trl) RED trv
      (CT_node A trrl BLACK trrv trrr)).

Definition RBT_Balance_result (A:Set) (tl:CTree A) (tc:Color) (tv:A) (tr:CTree A)
  (res:CTree A) :=
  (SomeRB tl -> SomeRB tr -> SomeRB res) /\
  (forall A_cmp (A_trans:Transitive A A_cmp) min max,
    IsBST A_cmp tl min tv ->
    A_cmp min tv ->
    A_cmp tv max ->
    IsBST A_cmp tr tv max ->
    IsBST A_cmp res min max) /\
  (forall e,
    ((IsMember e tl -> IsMember e res) /\
      (IsMember tv res) /\
      (IsMember e tr -> IsMember e res)) /\
    (IsMember e res ->
      IsMember e tl \/
      e = tv \/
      IsMember e tr)).

Theorem RBT_Balance_Result :
  forall (A:Set) (tl:CTree A) (tc:Color) (tv:A) (tr:CTree A) (res:CTree A),
    RBT_Balance A tl tc tv tr res ->
    RBT_Balance_result A tl tc tv tr res.
Proof.
  unfold RBT_Balance_result.
  intros.
  inversion H; clear H; subst.

  (* case 1 *)
  split. intros RBtl RBtr.
  destruct RBtl as [tln RBtl].
  destruct RBtr as [trn RBtr].
  inversion RBtl; subst; clear RBtl.
  rename H2 into RBtll.
  rename H3 into Ctll.
  rename H5 into RBtlr.
  rename H6 into Ctlr.
  inversion Ctll.

  split. intros A_cmp A_trans min max.
  intros BSTtl CMP_m_tv CMP_tv_m BSTtr.
  inversion BSTtl; subst; clear BSTtl.
  rename H6 into CMP_m_tlv.
  rename H7 into CMP_tlv_tv.
  rename H8 into BSTtlr.
  rename H3 into BSTtll.
  inversion BSTtll; subst; clear BSTtll.
  rename H3 into BSTtlll.
  rename H6 into CMP_m_tllv.
  rename H7 into CMP_tllv_tlv.
  rename H8 into BSTtllr.
  eapply IB_node; auto.
  eapply A_trans. apply CMP_tlv_tv. auto.

  split. split.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  split. eauto.
  intros MEMe. eauto.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  inversion H0; clear H0; subst; eauto.

  (* case 2 *)
  split. intros RBtl RBtr.
  destruct RBtl as [tln RBtl].
  destruct RBtr as [trn RBtr].
  inversion RBtl; subst; clear RBtl.
  rename H2 into RBtll.
  rename H3 into Ctll.
  rename H5 into RBtlr.
  rename H6 into Ctlr.
  inversion Ctlr.

  split. intros A_cmp A_trans min max.
  intros BSTtl CMP_m_tv CMP_tv_m BSTtr.
  inversion BSTtl; subst; clear BSTtl.
  rename H6 into CMP_m_tlv.
  rename H7 into CMP_tlv_tv.
  rename H8 into BSTtlr.
  rename H3 into BSTtll.
  inversion BSTtlr; subst; clear BSTtlr.
  rename H3 into BSTtlrl.
  rename H6 into CMP_tlv_tlrv.
  rename H7 into CMP_tlrv_tv.
  rename H8 into BSTtlrr.
  eapply IB_node; auto.
  eapply A_trans. apply CMP_m_tlv. auto.
  eapply A_trans. apply CMP_tlrv_tv. auto.

  split. split.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  split. eauto.
  intros MEMe. eauto.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  inversion H0; clear H0; subst; eauto.

  (* case 3 *)
  split. intros RBtl RBtr.
  destruct RBtl as [tln RBtl].
  destruct RBtr as [trn RBtr].
  inversion RBtr; subst; clear RBtr.
  rename H2 into RBtrl.
  rename H3 into Ctrl.
  rename H5 into RBtrr.
  rename H6 into Ctrr.
  inversion Ctrl.

  split. intros A_cmp A_trans min max.
  intros BSTtl CMP_m_tv CMP_tv_m BSTtr.
  inversion BSTtr; subst; clear BSTtr.
  rename H6 into CMP_tv_trv.
  rename H7 into CMP_trv_max.
  rename H8 into BSTtrr.
  rename H3 into BSTtrl.
  inversion BSTtrl; subst; clear BSTtrl.
  rename H3 into BSTtrll.
  rename H6 into CMP_tv_trlv.
  rename H7 into CMP_trlv_trv.
  rename H8 into BSTtrlr.
  eapply IB_node; auto.
  eapply A_trans. apply CMP_m_tv. auto.
  eapply A_trans. apply CMP_trlv_trv. auto.

  split. split.
  intros MEMe. eauto.
  split. eauto.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  inversion H0; clear H0; subst; eauto.

  (* case 4 *)
  split. intros RBtl RBtr.
  destruct RBtl as [tln RBtl].
  destruct RBtr as [trn RBtr].
  inversion RBtr; subst; clear RBtr.
  rename H2 into RBtrl.
  rename H3 into Ctrl.
  rename H5 into RBtrr.
  rename H6 into Ctrr.
  inversion Ctrr.

  split. intros A_cmp A_trans min max.
  intros BSTtl CMP_m_tv CMP_tv_m BSTtr.
  inversion BSTtr; subst; clear BSTtr.
  rename H6 into CMP_tv_trv.
  rename H7 into CMP_trv_max.
  rename H8 into BSTtrr.
  rename H3 into BSTtrl.
  inversion BSTtrr; subst; clear BSTtrr.
  rename H3 into BSTtrrl.
  rename H6 into CMP_trv_trrv.
  rename H7 into CMP_trrv_m.
  rename H8 into BSTtrrr.
  eapply IB_node; auto.
  eapply A_trans. apply CMP_m_tv. auto.

  split. split.
  intros MEMe. eauto.
  split. eauto.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  intros MEMe.
  inversion MEMe; clear MEMe; subst; eauto.
  inversion H0; clear H0; subst; eauto.
  inversion H0; clear H0; subst; eauto.
Qed.

Definition rbt_balance_worst := 42.
Definition rbt_balance_best := 8.

Definition rbt_balance_result (A:Set) (tl:CTree A) (tc:Color) (tv:A) (tr:CTree A)
  (res:CTree A) (c:nat) :=
  (rbt_balance_best <= c <= rbt_balance_worst).

Load "rbt_balance_gen.v".

Solve Obligations using
  unfold rbt_balance_result, rbt_balance_best, rbt_balance_worst;
    split; omega.

Solve Obligations using program_simpl.

(* 115 obligations later! *)

Definition minof {A:Set} (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_cmp_dec:forall (x y:A),
{ A_cmp x y } + { A_cmp y x }) (x:A) (y:A) : { r : A | A_cmp r x /\ A_cmp r y /\ (r = x \/ r = y) }.
Proof.
  destruct (A_cmp_dec x y) as [X | Y].
  exists x. split. apply A_refl. auto.
  exists y. split. auto. split. apply A_refl. auto.
Qed.

Lemma minof_left:
  forall (A:Set) (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_cmp_dec:forall (x y:A), { A_cmp x y } + { A_cmp y x }) (x:A) (y:A),
    A_cmp x y ->
    (` (minof A_cmp A_refl A_asym A_cmp_dec x y)) = x.
Proof.
  intros.
  destruct (minof A_cmp A_refl A_asym A_cmp_dec x y) as [r P].
  simpl.
  destruct P as [P1 [P2 [EQ | EQ]]]; subst; auto.
  apply A_asym in P1. contradiction.
Qed.

Lemma minof_right:
  forall (A:Set) (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_cmp_dec:forall (x y:A), { A_cmp x y } + { A_cmp y x }) (x:A) (y:A),
    A_cmp y x ->
    (` (minof A_cmp A_refl A_asym A_cmp_dec x y)) = y.
Proof.
  intros.
  destruct (minof A_cmp A_refl A_asym A_cmp_dec x y) as [r P].
  simpl.
  destruct P as [P1 [P2 [EQ | EQ]]]; subst; auto.
  apply A_asym in P2. contradiction.
Qed.

Definition maxof {A:Set} (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_cmp_dec:forall (x y:A),
{ A_cmp x y } + { A_cmp y x }) (x:A) (y:A) : { r : A | A_cmp x r /\ A_cmp y r /\ (r = x \/ r = y)}.
Proof.
  destruct (A_cmp_dec x y) as [X | Y].
  exists y. split. auto. split. apply A_refl. auto.
  exists x. split. apply A_refl. auto.
Qed.

Lemma maxof_right:
  forall (A:Set) (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_cmp_dec:forall (x y:A), { A_cmp x y } + { A_cmp y x }) (x:A) (y:A),
    A_cmp x y ->
    (` (maxof A_cmp A_refl A_asym A_cmp_dec x y)) = y.
Proof.
  intros.
  destruct (maxof A_cmp A_refl A_asym A_cmp_dec x y) as [r P].
  simpl.
  destruct P as [P1 [P2 [EQ | EQ]]]; subst; auto.
  apply A_asym in P2. contradiction.
Qed.

Lemma maxof_left:
  forall (A:Set) (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_cmp_dec:forall (x y:A), { A_cmp x y } + { A_cmp y x }) (x:A) (y:A),
    A_cmp y x ->
    (` (maxof A_cmp A_refl A_asym A_cmp_dec x y)) = x.
Proof.
  intros.
  destruct (maxof A_cmp A_refl A_asym A_cmp_dec x y) as [r P].
  simpl.
  destruct P as [P1 [P2 [EQ | EQ]]]; subst; auto.
  apply A_asym in P1. contradiction.
Qed.

Definition rbt_insert_inner_worst (h:nat) := (27 + rbt_balance_worst) * h + 8.
Definition rbt_insert_inner_best (h:nat) := 7.

Definition rbt_insert_inner_result (A:Set) (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_trans:Transitive A A_cmp) (A_cmp_dec:forall (x y:A),
{ A_cmp x y } + { A_cmp y x }) (A_eq_dec:forall (x y:A), { x = y } + { x <> y }) (ct:CTree A) (x:A) (res:CTree A) (c:nat) :=
(rbt_insert_inner_best (height ct) <= c <= rbt_insert_inner_worst (height ct)).

Load "rbt_insert_inner_gen.v".

Next Obligation.
Proof.
  unfold rbt_insert_inner_result, rbt_insert_inner_best, rbt_insert_inner_worst, rbt_balance_worst.
  simpl. omega.
Qed.

Next Obligation.
Proof.
  unfold rbt_insert_inner_result, rbt_insert_inner_best, rbt_insert_inner_worst, rbt_balance_worst.
  omega.
Qed.

Next Obligation.
Proof.
  clear am am0 H3 H2 Heq_anonymous0 Heq_anonymous.
  rename wildcard' into NEQ.
  rename wildcard'0 into CMPxv.
  unfold rbt_balance_result, rbt_balance_best, rbt_balance_worst in *.
  unfold rbt_insert_inner_result, rbt_insert_inner_best, rbt_insert_inner_worst, rbt_balance_worst in *.
  rename H0 into BAL_P.
  rename H1 into REC_P.
  simpl (height (CT_node A l c v r)).
  split. omega.
  rewrite mult_succ_r.
  apply max_case_strong; intros LE; omega.
Qed.

Next Obligation.
Proof.
  clear am am0 H3 H2 Heq_anonymous0 Heq_anonymous.
  rename wildcard' into NEQ.
  rename wildcard'0 into CMPxv.
  unfold rbt_balance_result, rbt_balance_best, rbt_balance_worst in *.
  unfold rbt_insert_inner_result, rbt_insert_inner_best, rbt_insert_inner_worst, rbt_balance_worst in *.
  rename H0 into BAL_P.
  rename H1 into REC_P.
  simpl (height (CT_node A l c v r)).
  split. omega.
  rewrite mult_succ_r.
  apply max_case_strong; intros LE; omega.
Qed.

Definition rbt_insert_worst (h:nat) := rbt_insert_inner_worst h + rbt_blacken_worst + 14.
Definition rbt_insert_best (h:nat) := 24.

Definition rbt_insert_result (A:Set) (A_cmp:A -> A -> Prop) (A_refl : forall x, A_cmp x x) (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x) (A_trans:Transitive A A_cmp) (A_cmp_dec:forall (x y:A),
  { A_cmp x y } + { A_cmp y x }) (A_eq_dec:forall (x y:A), { x = y } + { x <> y }) (ct:CTree A) (x:A) (res:CTree A) (c:nat) :=
(rbt_insert_best (height ct) <= c <= rbt_insert_worst (height ct)).

Load "rbt_insert_gen.v".

Next Obligation.
Proof.
  clear am H3 am0 H2.
  rename H0 into BLACKEN_P.
  rename H1 into INSERT_P.
  rename an into blacken_n.
  rename an0 into insert_n.
  unfold rbt_insert_result, rbt_insert_best, rbt_insert_worst in *.
  unfold rbt_insert_inner_result, rbt_insert_inner_best, rbt_insert_inner_worst, rbt_balance_worst in *.
  unfold rbt_blacken_result, rbt_blacken_best, rbt_blacken_worst in *.
  destruct BLACKEN_P as [RBres [Cres [BSTres [SMres BLACKEN_P]]]].
  omega.
Qed.

Corollary rbt_insert_time_worst_theta:
  big_theta rbt_insert_worst (fun n => n).
Proof.
  unfold rbt_insert_worst, rbt_insert_inner_worst, rbt_blacken_worst, rbt_balance_worst.
  simpl (27 + 42).
  eapply big_theta_trans.
  apply big_theta_eq.
  intros h.
  replace (69 * h + 8 + 8 + 14) with (69 * h + 30); try omega.
  reflexivity.
  apply big_theta_mult_plus.
Qed.
