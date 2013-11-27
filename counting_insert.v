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

Lemma div2_S : forall n, div2 (S (n + n)) = n.

Admitted.

Hint Rewrite div2_S.
Set Implicit Arguments.
Lemma invert_fl_log_S : forall n, fl_log_S (S n) = S (fl_log_S (div2 n)).
  intros.
  Check Fix_eq.
  Print Fix_eq.
  apply (Fix_eq _ lt (lt_wf) (fun _ => nat)).
  crush.
  destruct x.
  reflexivity.
  crush.
Qed.

Lemma double_div2 : forall n, div2 (n + n) = n.
  SearchAbout double.
  SearchAbout div2.
  
  apply (well_founded_ind lt_wf).
  intros.
  induction x.
  intuition.
  assert (S x + S x = S (S (x + x))); [omega | rewrite H0; clear H0].
  unfold div2.
  fold div2.
  assert (div2 (x + x) = x).
  apply H. omega.
  intuition.
Qed.
Hint Rewrite double_div2.

Lemma fl_log_S_odd :
  forall a:nat, fl_log_S (a+a+1) =
                (fl_log_S a) + 1.
  intros a.
  simpl.

  apply (well_founded_ind
           lt_wf
           (fun a => fl_log_S (a+a+1) = (fl_log_S a) + 1)).
  intros.
  rewrite plus_comm. simpl.

  assert (fl_log_S (S (x + x)) = S (fl_log_S (div2 (x + x)))).
  apply invert_fl_log_S.
  rewrite H0.
  assert (forall x, div2 (x + x) = x). apply double_div2.
  rewrite H1.
  omega.
Qed.

Lemma odd_div2 : (forall n, div2 (S (n + n)) = n).
  apply (well_founded_ind lt_wf).
  intros.
  destruct x.
  intuition.
  assert (S (S x + S x) = S (S (S x + x))); [omega | rewrite H0; clear H0].
  
  unfold div2 at 1.
  fold div2.
  assert (S x + x = S (x + x)) as H0; [omega | rewrite H0; clear H0].
  assert (div2 (S (x + x)) = x) as H0; [apply H; omega | rewrite H0; clear H0].
  reflexivity.
Qed.

Lemma fl_log_S_even :
  forall a:nat, fl_log_S ((a+1)+(a+1)) =
                (fl_log_S a) + 1.
  intros a.
  apply (well_founded_ind
           lt_wf
           (fun a =>
              fl_log_S ((a+1)+(a+1)) =
              (fl_log_S a) + 1)).
  intros.
  assert (x + 1 + (x + 1) = S (S (x + x))) as H0; [omega | rewrite H0; clear H0].
  assert (fl_log_S (S (S (x + x))) = S (fl_log_S (div2 (S (x + x))))).
  apply invert_fl_log_S.
  rewrite H0; clear H0.

  assert (fl_log_S (div2 (S (x + x))) = fl_log_S x); [ | omega].
  destruct x.
  compute; trivial.
  assert (div2 (S (S x + S x)) = S x) as H0; [apply odd_div2; omega | rewrite H0; clear H0 ].
  reflexivity.
Qed.

Theorem fl_log_S_same :
  forall (A:Set) n (b:braun_tree A n),
    bt_right_size b = fl_log_S n.
  induction b; intuition.
  simpl.
  intuition.
  crush.
  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases. omega.

  inversion TwoCases; subst.
  rewrite fl_log_S_odd.
  reflexivity.


  assert (t_size + 1 + t_size + 1 = (t_size+1) + (t_size+1)) as HH.
    omega. rewrite HH. clear HH.

  rewrite fl_log_S_even.
  reflexivity.
Qed.
