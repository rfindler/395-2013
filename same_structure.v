Require Import braun Omega.
Require Import Program.Equality.
Set Implicit Arguments.

Module same_structure.
Variable A : Type.

Inductive same_structure : 
  forall (n n' : nat),
    braun_tree A n -> braun_tree A n' -> Prop :=
| SEmpty : same_structure Empty Empty
| SNode : forall (x1 x2 : A) 
                 (nl1 nl2 nr1 nr2 : nat)
                 (h1 : nr1 <= nl1 <= nr1 + 1)
                 (h2 : nr2 <= nl2 <= nr2 + 1)
                 (l1 : braun_tree A nl1)
                 (l2 : braun_tree A nl2)
                 (r1 : braun_tree A nr1)
                 (r2 : braun_tree A nr2),
            same_structure l1 l2 -> 
            same_structure r1 r2 ->
            same_structure (Node x1 nl1 nr1 h1 l1 r1)
                           (Node x2 nl2 nr2 h2 l2 r2).

Theorem same_structure_same_size : 
  forall n1 n2 (b1 : braun_tree A n1) (b2 : braun_tree A n2),
    same_structure b1 b2 -> n1 = n2.
  intros n1 n2 b1 b2.
  induction 1; subst; reflexivity.
Qed.

Theorem same_size_same_structure :
  forall n (b1 b2 : braun_tree A n), 
    same_structure b1 b2.
  apply (well_founded_ind 
           lt_wf 
           (fun n => forall (b1 b2 : braun_tree A n), 
                       same_structure b1 b2)).
  intros x Ind b1 b2.
  dependent destruction b1; dependent destruction b2; intuition.

  constructor.

  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases. omega.
  assert (s_size0 = t_size0 \/ s_size0 = t_size0 + 1) as TwoCases'. omega.
  inversion TwoCases; inversion TwoCases'; intuition.

  assert (t_size = t_size0). omega. subst.
  apply JMeq.JMeq_eq in x. subst.
  constructor; apply Ind; omega.

  assert (t_size = t_size0). omega. subst.
  apply JMeq.JMeq_eq in x.
  subst.
  constructor; apply Ind; omega.
Qed.

End same_structure.
