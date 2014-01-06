Require Import Omega.
Require Import Braun.common.log.
Require Import Braun.common.le_util.
Require Import List.

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
