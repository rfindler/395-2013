Set Implicit Arguments.

Require Import CpdtTactics.
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

Eval simpl in 
    time (insert 1 
                 (Node 2 1 1 _
                       (Node 0 0 0 _ Empty Empty)
                       (Node 1 0 0 _ Empty Empty))).

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

Program Definition fl_log :
  nat -> nat := 
  Fix 
    lt_wf _
    (fun n fl_log => 
       match n with 
         | 0 => 0
         | S _ => 
           match even_odd_dec n with
             | right H =>
               (fl_log (proj1_sig 
                          (odd_S2n n H))
                       _)+1
             | left H => 
               (fl_log (proj1_sig 
                          (even_2n n H))
                       _)+1
           end
       end).

Obligation 1. apply lt_div2. induction wildcard'; crush. Qed.
Obligation 2. apply lt_div2. induction wildcard'; crush. Qed.

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
    fl_log
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16]
  = [0;1;2;2;3;3;3;3;4;4;4;4;4;4;4;4;5]%list.
 compute. reflexivity.
Qed.

Lemma fl_log_odd :
  forall a:nat, fl_log (a+a+1) = 
                (fl_log a) + 1.
  intros a.
  apply (well_founded_ind 
           lt_wf 
           (fun a => fl_log (a+a+1) = (fl_log a) + 1)).
  intros.
  rewrite plus_comm. simpl.
  unfold fl_log at 1.
  unfold Fix.
  simpl.
  Admitted.

(* this is almost certainly false *)
Lemma fl_log_even : 
  forall a:nat, fl_log ((a+1)+(a+1)) =
                (fl_log a) + 1.
  intros a.
  apply (well_founded_ind 
           lt_wf 
           (fun a => 
              fl_log ((a+1)+(a+1)) =
              (fl_log a) + 1)).
  Admitted.

Theorem fl_log_same : 
  forall (A:Set) n (b:braun_tree A n), 
    bt_right_size b = fl_log n.
  induction b; crush.
  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases. omega.

  inversion TwoCases; subst.
  rewrite fl_log_odd.
  reflexivity.
  

  assert (t_size + 1 + t_size + 1 = (t_size+1) + (t_size+1)) as HH. 
    omega. rewrite HH. clear HH.

  rewrite fl_log_even.
  reflexivity.
Qed.
