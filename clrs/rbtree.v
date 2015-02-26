Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Div2.
Require Import Relations_1.

Inductive Color : Set :=
| BLACK : Color
| RED : Color.
Hint Constructors Color.

Inductive CTree (A:Set) : Set :=
| CT_leaf :
  CTree A
| CT_node :
  CTree A -> Color -> A -> CTree A -> CTree A.
Hint Constructors CTree.

Fixpoint count {A:Set} (ct:CTree A) :=
  match ct with
    | CT_leaf =>
      0
    | CT_node l c v r =>
      count l + 1 + count r
  end.

Fixpoint height {A:Set} (ct:CTree A) :=
  match ct with
    | CT_leaf =>
      0
    | CT_node l c v r =>
      S (max (height l) (height r))
  end.

Inductive IsColor {A:Set} : CTree A -> Color -> Prop :=
| IC_leaf :
  IsColor (CT_leaf A) BLACK
| IC_node :
  forall l c v r,
    IsColor (CT_node A l c v r) c.
Hint Constructors IsColor.

Lemma IsColor_either:
  forall A (ct:CTree A),
    IsColor ct BLACK \/ IsColor ct RED.
Proof.
  intros.
  destruct ct; eauto.
  destruct c; eauto.
Qed.

Inductive IsRB {A:Set} : CTree A -> nat -> Prop :=
| IR_leaf :
  IsRB (CT_leaf A) 0
| IR_node_red :
  forall l v r n,
    IsRB l n ->
    IsColor l BLACK ->
    IsRB r n ->
    IsColor r BLACK ->
    IsRB (CT_node A l RED v r) n
| IR_node_black :
  forall l v r n,
    IsRB l n ->
    IsRB r n ->
    IsRB (CT_node A l BLACK v r) (S n).
Hint Constructors IsRB.

(* The total height cannot be more than twice the black height *)
Theorem IsRB_impl_height :
  forall A (ct:CTree A) n,
    IsRB ct n ->
    (IsColor ct BLACK ->
      n <= height ct <= 2 * n) /\
    (IsColor ct RED ->
      n <= height ct <= 2 * n + 1).
Proof.
  intros A ct n IR.
  induction IR; simpl in *.

  split; intros IC; omega.
  
  rename H into ICl.
  rename H0 into ICr.
  inversion IR1; clear IR1.
   subst l n.
   inversion IR2; clear IR2.
    subst r. simpl in *.
     split; intros IC.
      inversion IC.
      omega.
    subst r n. simpl in *. inversion ICr.
    subst l n0. inversion ICl.

   subst l n.
   inversion IR2; clear IR2.
    subst r n. inversion ICr.
    subst r n0.
    clear H H0 H2 H4.
    split; intros IC.
     inversion IC.
     destruct IHIR1 as [IHIR1 _].
     destruct IHIR2 as [IHIR2 _].
     apply IHIR1 in ICl.
     apply IHIR2 in ICr.
     apply max_case; omega.

  split; intros IC; [ | inversion IC].
  destruct IHIR1 as [IHIR1B IHIR1R].
  destruct IHIR2 as [IHIR2B IHIR2R].
  destruct (IsColor_either _ l) as [LB | LR];
    [ apply IHIR1B in LB | apply IHIR1R in LR ];
    (destruct (IsColor_either _ r) as [RB | RR];
      [ apply IHIR2B in RB | apply IHIR2R in RR ];
      apply max_case;
        omega).
Qed.

Theorem IsRB_impl_height_no_color :
  forall A (ct:CTree A) n,
    IsRB ct n ->
    n <= height ct <= 2 * n + 1.
Proof.
  intros A ct n RBt.
  destruct (IsRB_impl_height A ct n RBt) as [B R].
  destruct (IsColor_either A ct) as [Bt | Rt]; auto.
  apply B in Bt.
  omega.
Qed.

Lemma blacken_okay:
  forall A l c v r n,
    IsRB (CT_node A l c v r) n ->
    IsRB (CT_node A l BLACK v r) n \/
    IsRB (CT_node A l BLACK v r) (S n).
Proof.
  intros A l c v r n IR.
  inversion IR.

  subst. right. eauto.
  subst. left. eauto.
Qed.

Inductive IsBST {A:Set} (A_cmp:A -> A -> Prop) : CTree A -> A -> A -> Prop :=
| IB_leaf :
  forall min max,
    IsBST A_cmp (CT_leaf A) min max
| IB_node :
  forall min max l c v r,
    IsBST A_cmp l min v ->
    A_cmp min v ->
    A_cmp v max ->
    IsBST A_cmp r v max ->
    IsBST A_cmp (CT_node A l c v r) min max.
Hint Constructors IsBST.

Inductive IsMember {A:Set} (x:A) : CTree A -> Prop :=
| IM_node_left :
  forall l c v r,
    IsMember x l ->
    IsMember x (CT_node A l c v r)
| IM_node_right :
  forall l c v r,
    IsMember x r ->
    IsMember x (CT_node A l c v r)
| IM_node_eq :
  forall l c r,
    IsMember x (CT_node A l c x r).
Hint Constructors IsMember.

Lemma IsMember_impl_bounds :
  forall (A:Set) A_cmp ct (min_a max_a:A),
    Transitive A A_cmp ->
    IsBST A_cmp ct min_a max_a ->
    forall x,
      IsMember x ct ->
      (A_cmp min_a x /\ A_cmp x max_a).
Proof.
  intros A A_cmp ct min_a max_a A_cmp_trans BST.
  induction BST; intros x IM.
  inversion IM.
  rename H into CMPmv.
  rename H0 into CMPvm.
  inversion IM.
   subst. rename H0 into IMl. apply IHBST1 in IMl.
   destruct IMl as [IMl1 IMl2].
   split. auto.
   eapply A_cmp_trans. apply IMl2. auto.

   subst. rename H0 into IMr. apply IHBST2 in IMr.
   destruct IMr as [IMr1 IMr2].
   split; auto. eapply A_cmp_trans. apply CMPmv. auto.

   subst. auto.
 Qed.

(* This is based on the idea that the a complete binary tree contains *)
(* 2^h nodes and an incomplete tree just has some missing nodes. *)

Lemma le_exists:
  forall m n,
    n <= m ->
    { x | m = x + n }.
Proof.
 induction m as [|m]; intros n LE.
 exists 0. omega.
 destruct n as [|n].
 exists (S m). omega.
 edestruct (IHm n) as [x EQm].
 omega.
 subst m.
 clear IHm.
 exists x.
 omega.
Defined.

(* height | min_count | max_count *)
(* 0      | 0         | 0 *)
(* 1      | 1         | 1 *)
(* 2      | 3         | 4 *)

Lemma count_height_0:
  forall A (ct:CTree A),
    height ct = 0 -> count ct = 0.
Proof.
  intros A ct.
  destruct ct; simpl. auto.
  intros EQ. congruence.
Qed.

Lemma count_height_1:
  forall A (ct:CTree A),
    height ct = 1 -> count ct = 1.
Proof.
  intros A ct.
  destruct ct; simpl. auto.
  intros EQ. inversion EQ. clear EQ. generalize H0. clear H0.
  apply max_case_strong; intros LE EQ;
    (rewrite count_height_0; [ rewrite count_height_0; [ auto | ] | ]); omega.
Qed.  

Lemma pow_pos:
  forall n m,
    exists x,
      pow (S n) m = S x.
Proof.
  intros n m. generalize n. clear n. induction m; intros n.
  simpl. eauto.
  simpl.
  destruct (IHm n) as [x EQ].
  rewrite EQ. eexists.
  simpl. auto.
Qed.

Lemma count_pow_height:
  forall A (ct:CTree A),
    (* pred (2 * (height ct)) <= *)
    (count ct) <= (pred (pow 2 (height ct))).
Proof.
  intros A ct. induction ct.
  simpl. auto.

  simpl.
  replace (count ct1 + 1 + count ct2) with (S (count ct1 + count ct2)); try omega.
  rewrite plus_0_r.
  destruct (pow_pos 1 (height ct1)) as [phct1 EQphct1].
  rewrite EQphct1 in IHct1. simpl (pred (S phct1)) in IHct1.
  destruct (pow_pos 1 (height ct2)) as [phct2 EQphct2].
  rewrite EQphct2 in IHct2. simpl (pred (S phct2)) in IHct2.
  apply max_case_strong; intros LEh.

  rename ct2 into L. rename ct1 into H.
  rename IHct1 into IH_H. rename IHct2 into IH_L.
  rename EQphct1 into EQphH. rename EQphct2 into EQphL.
  rename phct1 into phH. rename phct2 into phL.
  
  rewrite EQphH. simpl.
  replace (phH + S phH) with (S (phH + phH)); try omega.
  apply le_n_S.
  apply le_add; auto.
  eapply le_trans. apply IH_L.
  apply le_S_n. rewrite <- EQphH. rewrite <- EQphL.
  apply pow2_monotone. auto.

  rename ct1 into L. rename ct2 into H.
  rename IHct2 into IH_H. rename IHct1 into IH_L.
  rename EQphct2 into EQphH. rename EQphct1 into EQphL.
  rename phct2 into phH. rename phct1 into phL.
  
  rewrite EQphH. simpl.
  replace (phH + S phH) with (S (phH + phH)); try omega.
  apply le_n_S.
  apply le_add; auto.
  eapply le_trans. apply IH_L.
  apply le_S_n. rewrite <- EQphH. rewrite <- EQphL.
  apply pow2_monotone. auto.
Qed.

Lemma rb_black_height_0:
  forall (A:Set) (t:CTree A),
    IsRB t 0 -> IsColor t BLACK ->
    t = CT_leaf A.
Proof.
  intros A t IR IC.
  inversion IR. auto.
  subst. inversion IC.
Qed.

Lemma rb_black_height_0_count:
  forall (A:Set) (t:CTree A),
    IsRB t 0 ->
    count t <= 1.
Proof.
  intros A t IR.
  
  inversion IR. auto.
  subst.
  rewrite (rb_black_height_0 A l H H0) in *.
  rewrite (rb_black_height_0 A r H1 H2) in *.
  simpl. auto.
Qed.
