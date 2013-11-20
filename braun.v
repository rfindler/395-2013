Require Import Arith List JMeq Omega.
Require Import Arith.Even Arith.Div2.
Require Import CpdtTactics Coq.Program.Wf.

Set Implicit Arguments.

Section braun_tree.

Variable A : Type.

Inductive braun_tree : nat -> Type :=
  | Empty : braun_tree 0
  | Node : forall (x:A) s_size t_size, 
             t_size <= s_size <= t_size+1 ->
             braun_tree s_size -> braun_tree t_size ->
             braun_tree (s_size+t_size+1).

Inductive same_structure : 
  forall (n n' : nat),
    braun_tree n -> braun_tree n' -> Prop :=
| SEmpty : same_structure Empty Empty
| SNode : forall (x1 x2 : A) 
                 (nl1 nl2 nr1 nr2 : nat)
                 (h1 : nr1 <= nl1 <= nr1 + 1)
                 (h2 : nr2 <= nl2 <= nr2 + 1)
                 (l1 : braun_tree nl1)
                 (l2 : braun_tree nl2)
                 (r1 : braun_tree nr1)
                 (r2 : braun_tree nr2),
            same_structure l1 l2 -> 
            same_structure r1 r2 ->
            same_structure (Node x1 h1 l1 r1)
                           (Node x2 h2 l2 r2).

Theorem same_structure_same_size : 
  forall n1 n2 (b1 : braun_tree n1) (b2 : braun_tree n2),
    same_structure b1 b2 -> n1 = n2.
  intros n1 n2 b1 b2.
  induction 1; subst; reflexivity.
Qed.

Theorem same_size_same_structure :
  forall n (b1 b2 : braun_tree n), 
    same_structure b1 b2.
  apply (well_founded_ind 
           lt_wf 
           (fun n => forall (b1 b2 : braun_tree n), same_structure b1 b2)).
  intros x Ind b1 b2.
  dep_destruct b1; dep_destruct b2; crush.
  constructor.

  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases. omega.
  assert (s_size0 = t_size0 \/ s_size0 = t_size0 + 1) as TwoCases'. omega.
  inversion TwoCases; inversion TwoCases'; crush.

  assert (t_size = t_size0). omega. subst.
  apply JMeq.JMeq_eq in x. subst.
  constructor; apply Ind; crush.

  assert (t_size = t_size0). crush. subst.
  apply JMeq.JMeq_eq in x.
  subst.
  constructor; apply Ind; crush.
Qed.

End braun_tree.

Implicit Arguments Empty [A].
Implicit Arguments Node [A].

Program Fixpoint insert A n (x:A)
        (b : braun_tree A n)
: braun_tree A (n+1) :=
  match b with
    | Empty => Node x 0 0 _ Empty Empty
    | Node y s_size t_size p s t => 
      Node x (t_size+1) s_size _ (insert y t) s
  end.

Obligation 2. omega. Qed.
Obligation 3. omega. Qed.

