Require Import Program.
Require Import Omega.
Require Import Braun.common.log.
Require Import Braun.common.util Braun.common.le_util.
Require Import Arith Arith.Even Arith.Div2 List.

Fixpoint man_time n : nat :=
  match n with
    | 0 => 0
    | S n' => man_time n' + (cl_log n)
  end.

Example man_time_ex :
  map man_time (1 :: 2 :: 3 :: 4 ::  5 ::  6 ::  7 ::  8 ::  9 :: 10 :: nil)
             = (1 :: 3 :: 5 :: 8 :: 11 :: 14 :: 17 :: 21 :: 25 :: 29 :: nil).
Proof.
  auto.
Qed.

Lemma man_time_nlogn :
  forall n,
    man_time n <= n * cl_log n.
Proof.
  induction n as [|n].

  simpl; omega.

  replace (S n * cl_log (S n)) with (n * cl_log (S n) + cl_log (S n));
    [|unfold mult; fold mult; omega].
  unfold man_time; fold man_time.
  apply le_plus_left.
  apply (le_trans (man_time n)
                  (n * cl_log n)
                  (n * cl_log (S n))).
  assumption.
  
  apply le_mult_right.
  apply cl_log_monotone.
Qed.
Hint Resolve man_time_nlogn.

(* this is http://oeis.org/A001855 *)
Program Fixpoint mat_time n {measure n} :=
  match n with
    | O => 0
    | S n' =>
      mat_time (div2 n) + mat_time (div2 n') + n
  end.

Lemma mat_time_Sn : 
  forall n',
    mat_time (S n') = 
    mat_time (div2 (S n')) +
    mat_time (div2 n') +
    (S n').
Proof.
  intros.
  WfExtensionality.unfold_sub 
    mat_time
    (mat_time (S n')).
  auto.
Qed.

Lemma mat_time_Sn_cl_log : 
  forall n : nat,
    mat_time (S n) = mat_time n + cl_log (S n).
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => mat_time (S n) = mat_time n + cl_log (S n))).

  intros n IHn.
  
  destruct n.
  compute;reflexivity.

  rewrite mat_time_Sn.

  replace (div2 (S (S n))) with (S (div2 n));[|unfold div2;reflexivity].

  rewrite IHn;auto.

  replace (cl_log (S (S n))) with (S (cl_log (div2 (S (S n)))));
    [|symmetry;apply cl_log_div2'].
  
  rewrite mat_time_Sn.
  
  replace (div2 (S (S n))) with (S (div2 n));[|unfold div2;reflexivity].

  omega.
Qed.

Lemma rt_naive_same_as_mat_time :
  forall n, mat_time n = man_time n.
Proof.
  induction n.
  auto.
  
  simpl; rewrite <- IHn; apply mat_time_Sn_cl_log; auto.
Qed.

Lemma braun_implies_mat_time:
  forall x y,
    y <= x <= y + 1 ->
    x + y + mat_time x + mat_time y + 1 = mat_time (S (x + y)).
Proof.
  intros x y BTI.
  rewrite mat_time_Sn.

  assert (x = y \/ x = y+1) as TWOCASES;[omega|clear BTI].
  destruct TWOCASES; subst x.

  rewrite div2_with_odd_argument.
  rewrite double_div2.
  omega.

  replace (S (y + 1 + y)) with ((y+1)+(y+1));[|omega].
  replace (y+1+y) with (S (y + y));[|omega].
  rewrite div2_with_odd_argument.
  rewrite double_div2.
  omega.
Qed.
Hint Resolve braun_implies_mat_time.

Lemma mat_time_nlogn : 
  forall n,
    mat_time n <= n * cl_log n.
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => mat_time n <= n * cl_log n)).
  intros n IND.
  destruct n. 
  compute;constructor.

  rewrite mat_time_Sn.

  apply (le_trans (mat_time (div2 (S n)) + mat_time (div2 n) + S n)
                  (div2 (S n) * cl_log (div2 (S n)) + 
                   (div2 n) * cl_log (div2 n) +
                   S n)
                  (S n * cl_log (S n))).
  apply le_plus_left.

  assert (mat_time (div2 (S n)) <= div2 (S n) * cl_log (div2 (S n)));
    [apply IND; auto|].
  assert (mat_time (div2 n) <=  div2 n * cl_log (div2 n));
    [apply IND;auto|].
  omega.

  rewrite cl_log_div2'.
  assert (S n * S (cl_log (div2 (S n))) = (S n) * cl_log (div2 (S n)) + S n) as H;
    [rewrite mult_comm;
     unfold mult at 1;fold mult;
     rewrite plus_comm;
     rewrite mult_comm;
     reflexivity|rewrite H;clear H].

  apply le_plus_left.

  apply (le_trans
           (div2 (S n) * cl_log (div2 (S n)) + div2 n * cl_log (div2 n))
           (div2 (S n) * cl_log (div2 (S n)) + div2 (S n) * cl_log (div2 (S n)))
           (S n * cl_log (div2 (S n)))).

  apply le_plus_right.

  apply le_pieces_le_prod.
  apply div2_monotone.
  
  assert (even n \/ odd n) as H; [apply even_or_odd|destruct H].
  rewrite even_div2;[|assumption].
  constructor.

  rewrite <- odd_div2;[|assumption].
  apply cl_log_monotone.

  rewrite mult_comm.
  replace (S n * cl_log (div2 (S n))) with (cl_log (div2 (S n)) * S n);[|apply mult_comm].
  apply div2_mult.
Qed.
