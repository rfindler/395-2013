Set Implicit Arguments.

Require Import braun util monad.
Require Import Arith Omega Coq.Logic.JMeq.

Program Fixpoint insert (A:Set) n (x:A)
        (b : braun_tree A n)
: C (braun_tree A (n+1)) :=
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

Program Example insert_example : 
  time (insert 1
               (Node 2 1 1 _
             	     (Node 0 0 0 _ Empty Empty)
                     (Node 1 0 0 _ Empty Empty)))
       = 3.
compute. reflexivity.
Qed.

Fixpoint bt_right_size (A:Set) n
         (b : braun_tree A n) : nat :=
  match b with
    | Empty => 0
    | Node x _ _ _ s t =>
      bt_right_size t + 1
  end.

Theorem insert_time :
  forall (A:Set) n (x:A)
         (b : braun_tree A n),
    time (insert x b) =
    bt_right_size b + 1.

  intros.
  generalize dependent x.
  induction b.
  reflexivity.
  intros.
  simpl.
  unfold bind.
  remember (insert x b2) as x1.
  destruct x1. simpl.
  assert (n = snd (insert x b2)).
  inversion Heqx1.
  reflexivity.
  rewrite H.
  rewrite IHb2.
  reflexivity.
Qed.

Require Import Arith.Even Arith.Div2.
(* What we want is a function `f` that satisfies these properties:
    f(0) = 0
    f(n + n + 1) = f(n) + 1
    f((n+1)+(n+1)) = f(n) + 1

   That function is f(n) = floor(log_2(S n)) since:
   f(0) = floor(log_2(S 0))
        = floor(log_2(1)) 
        = floor(0)
        = 0

   f(2n+1) = floor(log_2(S (2n + 1)))
           = floor(log_2(2 * (n+1)))
           = floor(log_2(2) + log_2(n+1))
           = floor(S (log_2(n+1)))
           = floor(log_2(n+1)) + 1
           = S (floor(log_2(S n)))
           = S (f(n)) (specification)

   f(2n+2) = floor(log_2(S (2n + 2)))
           = floor(log_2(2n + 3))
           = floor(log_2(2n + 2)) (since an odd number cannot be a power of 2)
           = floor(log_2(n+1)) + 1 (by the previous case)
           = S (floor(log_2(S n)))
           = S (f(n))

   Rearranging a bit we get the following definition:
 *)
Require Import Coq.Program.Wf.
Program Fixpoint fl_log_S n {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S n' => S (fl_log_S (div2 n'))
  end.

Require Lists.List.
Require Import Program.Syntax.

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
  = [0;1;1;2;2;2;2;3;3;3;3;3;3;3;3;4]%list.
 compute. reflexivity.
Qed.

Set Implicit Arguments.

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
  apply (Fix_eq _ lt (lt_wf) (fun _ => nat)).
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

Theorem fl_log_S_same :
  forall (A : Set) n (b:braun_tree A n), bt_right_size b = fl_log_S n.
  
  induction b; intuition; simpl.
  rewrite IHb2; clear IHb1 IHb2 b1 b2.
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
