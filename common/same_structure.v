(* prove that there can be only one
   shape braun tree for a given size *)

Require Import Braun.common.braun Braun.common.util Omega.
Require Import Program.Equality.
Set Implicit Arguments.

Inductive same_structure {A:Set} : @bin_tree A -> @bin_tree A -> Prop :=
| SS_mt :
    same_structure bt_mt bt_mt
| SS_node :
    forall (x1 x2 : A) l1 l2 r1 r2,
      same_structure l1 l2 ->
      same_structure r1 r2 ->
      same_structure (bt_node x1 l1 r1)
                     (bt_node x2 l2 r2).
Hint Constructors same_structure.

Theorem same_structure_same_size :
  forall A (bt1:@bin_tree A) bt2,
    same_structure bt1 bt2 ->
    forall n1 n2,
      Braun bt1 n1 ->
      Braun bt2 n2 ->
      n1 = n2.
Proof.
  intros A bt1 bt2 SS.
  induction SS; intros n1 n2 B1 B2;
  inversion_clear B1;
  inversion_clear B2; eauto.
Qed.
Hint Rewrite same_structure_same_size.

Theorem same_size_same_structure :
  forall A n (bt1:@bin_tree A) bt2,
    Braun bt1 n ->
    Braun bt2 n ->
    same_structure bt1 bt2.
Proof.
  intros A.
  apply (well_founded_ind
           lt_wf
           (fun n => forall (b1 b2 : bin_tree),
                       Braun b1 n -> Braun b2 n -> same_structure b1 b2)).
  intros n IH bt1 bt2 B1 B2.
  dependent destruction bt1; dependent destruction bt2; eauto;
  inversion B1; subst;
  inversion B2; subst; eauto.

  apply plusone_ne_zero in H2; inversion H2.
  symmetry in H. apply plusone_ne_zero in H; inversion H.
  assert (s_size = s_size0); try omega.
  assert (t_size = t_size0); try omega.
  subst.

  eapply SS_node.
  eapply IH; eauto; omega.
  eapply IH; eauto; omega.
Qed.
Hint Resolve same_size_same_structure.
