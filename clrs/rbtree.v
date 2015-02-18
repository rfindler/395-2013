Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Relations_1.
Require Import Braun.clrs.fib.

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

Definition bst_search_time (n:nat) :=
  3 * n + 2.

Program Fixpoint bst_search {A:Set}
  (A_cmp:A -> A -> Prop)
  (A_asym:forall x y, A_cmp x y -> ~ A_cmp y x)
  (A_trans:Transitive A A_cmp)
  (A_cmp_dec:
    forall (x y:A),
      { A_cmp x y } + { A_cmp y x })
  (A_eq_dec:
    forall (x y:A),
      { x = y } + { x <> y })
  (x:A) (ct:CTree A) :
  {! res !:! bool !<! c !>!
    forall (min_a max_a:A)
      (MIN:A_cmp min_a x)
      (MAX:A_cmp x max_a)
      (BST:IsBST A_cmp ct min_a max_a),
    (res = true -> IsMember x ct) /\
    (res = false -> ~ IsMember x ct) /\
    1 <= c <= bst_search_time (height ct) !}
  :=
  match ct with
    | CT_leaf =>
      += 1;
      <== false
    | CT_node l c v r =>
      match A_eq_dec x v with
        | left _ =>
          += 2 ;
          <== true
        | right _ =>
          match A_cmp_dec x v with
            | left _ =>
              res <- bst_search A_cmp A_asym A_trans A_cmp_dec A_eq_dec x l ;
              += 3 ;
              <== res
            | right _ =>
              res <- bst_search A_cmp A_asym A_trans A_cmp_dec A_eq_dec x r ;
              += 3 ;
              <== res
          end
      end
  end.

Next Obligation.
 unfold bst_search_time.
 split.
 intros EQ. inversion EQ.
 split; try omega.
 intros _ IM.
 inversion IM.
Qed.

Next Obligation.
  unfold bst_search_time.
  split.
  intros _. eauto.
  split.
  intros EQ. congruence.
  omega.
Qed.

Obligation Tactic := idtac.
Next Obligation.
  unfold bst_search_time.
  intros A A_cmp A_asym A_trans A_cmp_dec A_eq_dec x ct.
  intros l c v r EQ. subst ct.
  intros NEQ _ CMPxv _.
  intros res.
  intros _.
  intros xm EQ. simpl in EQ. subst xm.
  intros an REC.
  intros min_a max_a CMPax CMPxa BST.
  edestruct REC as [IMt [IMf AN]].
   apply CMPax.
   apply CMPxv.
   inversion BST. subst. auto.
  clear REC.

  split.
  intros EQ. apply IMt in EQ. eauto.
  split.
  intros EQ. apply IMf in EQ.
  intros IM. inversion IM; subst; auto.
  rename H0 into IMr.
  inversion BST.
  subst.
  rename H3 into BSTl.
  rename H6 into CMPav.
  rename H7 into CMPva.
  rename H8 into BSTr.
  
  edestruct IsMember_impl_bounds.
  apply A_trans.
  apply BSTr.
  apply IMr.
  rename H into CMPvx.
  clear H0.
  eapply A_asym.
  apply CMPvx.
  auto.

  simpl (height (CT_node A l c v r)).
  remember (height l) as L.
  remember (height r) as R.
  clear HeqR HeqL IMf IMt CMPxv NEQ BST r v c l CMPxa CMPax max_a min_a x A_eq_dec
    A_cmp_dec A_trans A_asym A_cmp A res.
  apply max_case_strong.
  intros LE. clear LE R. omega.
  intros LE. omega.
Qed.
Obligation Tactic := program_simpl.

Obligation Tactic := idtac.
Next Obligation.
  unfold bst_search_time.
  intros A A_cmp A_asym A_trans A_cmp_dec A_eq_dec x ct.
  intros l c v r EQ. subst ct.
  intros NEQ _ CMPvx _.
  intros res.
  intros _.
  intros xm EQ. simpl in EQ. subst xm.
  intros an REC.
  intros min_a max_a CMPax CMPxa BST.
  edestruct REC as [IMt [IMf AN]].
   apply CMPvx.
   apply CMPxa.
   inversion BST. subst. auto.
  clear REC.
  split.
  intros EQ. apply IMt in EQ. eauto.
  split.
  intros EQ. apply IMf in EQ.
  intros IM. inversion IM; subst; auto.
  rename H0 into IMl.
  inversion BST.
  subst.
  rename H3 into BSTl.
  rename H6 into CMPav.
  rename H7 into CMPva.
  rename H8 into BSTr.
  
  edestruct IsMember_impl_bounds.
  apply A_trans.
  apply BSTl.
  apply IMl.
  clear H.
  rename H0 into CMPxv.
  eapply A_asym.
  apply CMPvx.
  auto.

  simpl (height (CT_node A l c v r)).
  remember (height l) as L.
  remember (height r) as R.
  clear HeqR HeqL IMf IMt CMPvx NEQ BST r v c l CMPxa CMPax max_a min_a x A_eq_dec
    A_cmp_dec A_trans A_asym A_cmp A res.
  apply max_case_strong.
  intros LE. omega.
  intros LE. clear LE L. omega.
Qed.
Obligation Tactic := program_simpl.

Corollary rbbst_search_time_bound_black_height:
  forall A (ct:CTree A) n,
    IsRB ct n ->
    bst_search_time (height ct) <= 6 * n + 5.
Proof.
  intros A ct n IR.
  unfold bst_search_time.
  apply IsRB_impl_height_no_color in IR.
  omega.
Qed.

(* The theorem above is actually not that strong because we really
   want to relate the runtime the number of elements in the set. We've
   previously shown that the black-height is related to the actual
   height. We really need to relate the height to the count. *)

(* This is based on the idea that the a complete binary tree contains
   2^h nodes and an incomplete tree just has some missing nodes. *)

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

Lemma count_pow_height':
  forall
    (A : Set)
    (ct1 : CTree A)
    (ct2 : CTree A)
    (IHct1 : count ct1 <= pow 2 (height ct1))
    (IHct2 : count ct2 <= pow 2 (height ct2))
    (LEh :    height ct2 <= height ct1),
   count ct1 + 1 + count ct2 <= S (S (pow 2 (height ct1))).
Proof.
  intros.
  eapply le_trans.
  eapply le_add.
  eapply le_add.
  apply IHct1.
  auto.
  apply IHct2.
  clear IHct1 IHct2.
  remember (height ct2) as L.
  remember (height ct1) as R.
  clear A ct1 ct2 HeqL HeqR.
  apply le_exists in LEh.
  destruct LEh as [x EQr]. subst R.

Admitted.

Lemma count_pow_height:
  forall A (ct:CTree A),
    count ct <= pow 2 (height ct).
Proof.
  intros A.
  induction ct.

  simpl. auto.

  simpl.
  apply max_case_strong; intros LEh.
  apply count_pow_height'; auto.

  replace (count ct1 + 1 + count ct2) with (count ct2 + 1 + count ct1); try omega.
  apply count_pow_height'; auto.
Qed.

(* This is the inversion of the above, except that it is actually only
   true when the tree is balanced, which rb trees are. (Maybe should
   be fl_log?) *)

Lemma height_log_case':
  forall
    (A : Set)
    (l : CTree A)
    (r : CTree A)
    (n : nat)
    (RBl : IsRB l n)
    (RBr : IsRB r n)
    (IHl : height l <= 2 * cl_log (count l + 1))
    (IHr : height r <= 2 * cl_log (count r + 1))
    (LEh : height r <= height l),
    S (height l) <= 2 * cl_log (count l + count r + 1 + 1).
Proof.
  intros.

  apply IsRB_impl_height_no_color in RBl.
  apply IsRB_impl_height_no_color in RBr.
  
  cut (2 * cl_log (count l + 1 + count l + 1) <= 2 * cl_log (count l + count r + 1 + 1)).
  intros LEc.
  eapply le_trans; [|apply LEc].
  rewrite <- cl_log_even.
  omega.
  apply le_mult. auto.
  apply cl_log_monotone.
  apply le_add; auto.
  replace (count l + 1 + count l) with (count l + count l + 1); try omega.
  apply le_add; auto.
  apply le_add; auto.

Admitted.

Lemma height_log_case:
  forall A (l r:CTree A) n,
    IsRB l n ->
    IsRB r n ->
    height l <= 2 * cl_log (count l + 1) ->
    height r <= 2 * cl_log (count r + 1) ->
    S (max (height l) (height r)) <= 2 * cl_log (count l + 1 + count r + 1).
Proof.
  intros A l r n RBl RBr IHl IHr.
  replace (count l + 1 + count r + 1 ) with (count l + count r + 1 + 1); try omega.

  eapply max_case_strong.
  apply height_log_case' with (n:=n); auto.
  replace (count l + count r + 1) with (count r + count l + 1); try omega.
  apply height_log_case' with (n:=n); auto.
Qed.

Lemma height_log_count:
  forall A (ct:CTree A) n,
    IsRB ct n ->
    height ct <= 2 * cl_log (count ct + 1).
Proof.
  intros A ct n IR.
  induction IR.

  simpl. auto.

  simpl (height (CT_node A l RED v r)).
  simpl (count (CT_node A l RED v r)).
  apply height_log_case with (n := n); auto.

  simpl (height (CT_node A l BLACK v r)).
  simpl (count (CT_node A l BLACK v r)).
  apply height_log_case with (n := n); auto.
Qed.

(* Finally, here is how CLRS puts it:

   Lemma 13.1: A red-black tree with n internal nodes has height at
   most 2 * lg(n + 1)

   This proof embeds the proof about a bound on the black-height.

 *)

(* Assuming we can do one of those, then we can prove this: *)

Lemma rb_black_height_impl_count:
  forall (A : Set)
    (ct : CTree A)
    (n : nat)
    (IR : IsRB ct n),
    n <= cl_log (count ct + 1).
Proof.
  intros A ct n IR.
  induction IR. omega.

  simpl.

Admitted.

Corollary rbbst_search_time_bound_count:
  forall A (ct:CTree A) n,
    IsRB ct n ->
    bst_search_time (height ct) <= 6 * cl_log (count ct + 1) + 5.
Proof.
  intros A ct n IR.
  eapply le_trans.
  apply rbbst_search_time_bound_black_height.
  apply IR.
  apply le_add; auto.
  apply le_mult; auto.
  apply rb_black_height_impl_count.
  auto.
Qed.
