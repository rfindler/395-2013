Set Implicit Arguments.

Require Import braun util monad2.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.
Require Import Program.Syntax.

Program Fixpoint fl_log_S n {wf lt n} : nat :=
  match n with
    | 0 => 1
    | S n' => S (fl_log_S (div2 n'))
  end.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint map (s : list A) : list B :=
    match s with
      | nil => nil
      | cons h t => cons (f h) (map t)
    end.
End map.

Example rs_ex :
  map
    fl_log_S
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
  = [1;2;2;3;3;3;3;4;4;4;4; 4; 4; 4; 4; 5]%list.
 compute. reflexivity.
Qed.

(* 
   First a couple of useful lemmas about div2 that aren't in the stdlib
   for some reason. 
*)
Lemma double_div2 : forall n, div2 (n + n) = n.
  induction n.
  compute; reflexivity.
  assert (S n + S n = S (S (n + n))) as H0; [omega | rewrite H0; clear H0].
  unfold div2; fold div2.
  rewrite IHn.
  reflexivity.
Qed.

Lemma odd_div2 : (forall n, div2 (S (n + n)) = n).
  induction n.
  compute; reflexivity.
  assert (S (S n + S n) = S (S (S n + n))) as H0; [omega | rewrite H0; clear H0].
  unfold div2 at 1.
  fold div2.
  assert (S n + n = S (n + n)) as H0; [omega | rewrite H0; clear H0].
  rewrite IHn.
  reflexivity.
Qed.

Lemma invert_fl_log_S_S : forall n, fl_log_S (S n) = S (fl_log_S (div2 n)).
  intros.
  apply (Fix_eq _ lt lt_wf (fun _ => nat)).
  intuition.
  destruct x; [ reflexivity | repeat f_equal].
Qed.

Lemma fl_log_S_odd :
  forall n : nat, fl_log_S (n + n + 1) = (fl_log_S n) + 1.
  intro n.
  rewrite plus_comm; simpl.
  rewrite invert_fl_log_S_S.
  rewrite double_div2.
  rewrite plus_comm; simpl; reflexivity.
Qed.

Lemma fl_log_S_even :
  forall n : nat, fl_log_S ((n + 1) + (n + 1)) = (fl_log_S n) + 1.
  intro n.
  assert (n + 1 + (n + 1) = S (S (n + n))) as H0; [omega | rewrite H0; clear H0].
  rewrite invert_fl_log_S_S.
  rewrite odd_div2.
  rewrite plus_comm; simpl; reflexivity.
Qed.



Program Fixpoint insert (A:Set) n (x:A)
        (b : braun_tree A n)
: C (braun_tree A (n+1)) (fl_log_S n) :=
  match b with
    | Empty =>
      ++1 ;
        ret (Node x 0 0 _ Empty Empty)
    | Node y s_size t_size p s t =>
      st <- (insert y t);
        ++ 1;
        ret (Node x
                  (t_size+1) s_size
                  _
                  st s)
  end.

Solve Obligations using (intros;omega).

Obligation 4.
  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases;
    [ omega | ].

  inversion TwoCases; subst; clear.
  
  rewrite fl_log_S_odd.
  reflexivity.

  assert (t_size + 1 + t_size + 1 = (t_size+1) + (t_size+1)) as H0;
    [ omega | rewrite H0; clear H0].

  rewrite fl_log_S_even.
  reflexivity.
Qed.
