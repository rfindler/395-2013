Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax List.
Require Import Braun.common.util.

Set Implicit Arguments.

(* fl_log(n) = floor(log_2(n+1)) *)
Program Fixpoint fl_log n {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S n' => S (fl_log (div2 n'))
  end.

(* cl_log(n) = ceiling(log_2(n+1)) *)
(* which is the same as Racket's 'integer-length' *)
Program Fixpoint cl_log n {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S n' => S (cl_log (div2 n))
  end.

Example fl_log_ex :
  map fl_log
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
  = [0;1;1;2;2;2;2;3;3;3;3; 3; 3; 3; 3; 4].
Proof.
  compute; reflexivity.
Qed.

Example cl_log_ex :
  map cl_log
      [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
  = [0;1;2;2;3;3;3;3;4;4;4; 4; 4; 4; 4; 4].
Proof.
  compute; reflexivity.
Qed.

Lemma fl_log_div2' : 
  forall n,
    fl_log (S n) = S (fl_log (div2 n)).
Proof.
  intros.
  apply (Fix_eq _ lt lt_wf (fun _ => nat)).
  intuition.
  destruct x; [ reflexivity | repeat f_equal].
Qed.
Hint Rewrite fl_log_div2'.

Lemma fl_log_div2'' :  forall n, div2 (n + 1) < S n.
Proof.
  intros n.
  replace (n+1) with (S n);[|omega].
  auto.
Qed.
Hint Resolve fl_log_div2''.

Lemma cl_log_div2' : 
  forall n, 
    cl_log (S n) = S (cl_log (div2 (S n))).
Proof.
  intros.
  apply (Fix_eq _ lt lt_wf (fun _ => nat)).
  intuition.
  destruct x; [ reflexivity | repeat f_equal].
Qed.
Hint Rewrite cl_log_div2'.

Lemma fl_log_zero :
  fl_log 0 = 0.
Proof.
  apply (Fix_eq _ lt lt_wf (fun _ => nat)).
  intuition.
  destruct x; [ reflexivity | repeat f_equal].
Qed.
Hint Rewrite fl_log_zero.

Lemma fl_log_div2 : 
  forall n, 
    fl_log (div2 n) + 1 = fl_log (S n).
Proof.
  intros n.
  rewrite fl_log_div2'.
  intuition.
Qed.
Hint Rewrite fl_log_div2.

Lemma fl_log_odd :
  forall n : nat,
    fl_log (n + n + 1) = (fl_log n) + 1.
Proof.
  intro n.
  rewrite plus_comm; simpl.
  rewrite fl_log_div2'.
  rewrite double_div2.
  rewrite plus_comm; simpl; reflexivity.
Qed.
Hint Rewrite fl_log_odd.

Lemma fl_log_even :
  forall n : nat,
    fl_log ((n + 1) + (n + 1)) = (fl_log n) + 1.
Proof.
  intro n.
  replace (n + 1 + (n + 1)) with (S (S (n + n))) ; [|omega].
  rewrite fl_log_div2'.
  rewrite div2_with_odd_argument.
  rewrite plus_comm; simpl; reflexivity.
Qed.
Hint Rewrite fl_log_even.

Lemma cl_log_odd :
  forall n,
    cl_log(n+n+1) = cl_log n + 1.
Proof.
  intros.
  rewrite plus_comm; simpl.
  rewrite cl_log_div2'.
  rewrite div2_with_odd_argument.
  rewrite plus_comm; simpl; reflexivity.
Qed.
Hint Rewrite cl_log_odd.

Lemma cl_log_even :
  forall n,  
    cl_log (n+1) + 1 = cl_log (n + 1 + n + 1).
Proof.
  intros.
  replace (n + 1 + n + 1) with (S (S (n+n))); [|omega].
  rewrite cl_log_div2'.
  replace (S (S (n+n))) with ((n+1)+(n+1)); [|omega].
  rewrite double_div2.
  rewrite plus_comm; simpl; reflexivity.
Qed.
Hint Rewrite cl_log_even.

Lemma braun_invariant_implies_fl_log_property :
  forall s_size t_size,
    t_size <= s_size <= t_size + 1 ->
    fl_log t_size + 1 = fl_log (s_size + t_size + 1).
Proof.
  intros.
  assert (s_size = t_size \/ s_size = t_size + 1) as TwoCases;
    [ omega | ].

  inversion TwoCases; subst; clear.

  rewrite fl_log_odd.
  reflexivity.

  replace (t_size + 1 + t_size + 1) with ((t_size+1) + (t_size+1)); [| omega].
  rewrite fl_log_even.
  reflexivity.
Qed.
Hint Rewrite braun_invariant_implies_fl_log_property.

Lemma braun_invariant_implies_cl_log_property:
  forall s1_size t1_size,
    t1_size <= s1_size <= t1_size + 1 ->
    cl_log s1_size + 1 = cl_log (s1_size + t1_size + 1).
Proof.
  intros.
  assert (s1_size = t1_size \/ s1_size = t1_size+1) as TWOCASES; [omega|].
  inversion TWOCASES; clear TWOCASES; subst s1_size.

  replace (cl_log (t1_size + t1_size+1)) with (cl_log (S (t1_size + t1_size))).

  replace (cl_log (S (t1_size + t1_size)))
  with (S (cl_log (div2 (S (t1_size + t1_size))))) ; [|rewrite cl_log_div2';reflexivity].

  replace (div2 (S (t1_size+t1_size))) with t1_size;
    [| rewrite (div2_with_odd_input t1_size); reflexivity].

  omega.

  replace (t1_size + t1_size+1) with (S (t1_size+t1_size)).
  reflexivity.

  omega.

  replace (t1_size + 1 + t1_size + 1) with (S (S (t1_size+t1_size))); [|omega].
  rewrite cl_log_div2'.

  replace (S (S (t1_size+t1_size))) with ((S t1_size)+(S t1_size)); [|omega].
  rewrite double_div2.
  rewrite plus_comm.
  simpl.
  rewrite plus_comm.
  reflexivity.
Qed.
Hint Rewrite braun_invariant_implies_cl_log_property.

Lemma fl_log_cl_log_relationship :
  forall n,
    S (fl_log n) = cl_log (S n).
Proof.
  apply (well_founded_ind
           lt_wf
           (fun n => S (fl_log n) = cl_log (S n))).
  intros.
  destruct x.
  compute; reflexivity.
  rewrite fl_log_div2'.
  rewrite cl_log_div2'.
  rewrite (H (div2 x)); auto.
Qed.
Hint Rewrite fl_log_cl_log_relationship.

