Require Import Program.
Require Import Omega.
Require Import Braun.common.log.
Require Import Braun.common.le_util.
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
