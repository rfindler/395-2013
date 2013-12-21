Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax.
Require Import util.

Set Implicit Arguments.

Section fl_log.

  Program Fixpoint fl_log n {wf lt n} : nat :=
    match n with
      | 0 => 0
      | S n' => S (fl_log (div2 n'))
    end.

  Program Fixpoint cl_log n {wf lt n} : nat :=
    match n with
      | 0 => 0
      | S n' => S (cl_log (div2 n))
    end.

  Section map.
    Variables P Q : Type.
    Variable f : P -> Q.

    Fixpoint map (s : list P) : list Q :=
      match s with
        | nil => nil
        | cons h t => cons (f h) (map t)
      end.
  End map.

  Example fl_log_ex :
    map fl_log
        [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
      = [0;1;1;2;2;2;2;3;3;3;3; 3; 3; 3; 3; 4]%list.
  compute; reflexivity.
  Qed.

  Example cl_log_ex :
    map cl_log
        [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
      = [0;1;2;2;3;3;3;3;4;4;4; 4; 4; 4; 4; 4]%list.
  compute; reflexivity.
  Qed.

  Lemma fl_log_div2' : forall n, fl_log (S n) = S (fl_log (div2 n)).
    intros.
    apply (Fix_eq _ lt lt_wf (fun _ => nat)).
    intuition.
    destruct x; [ reflexivity | repeat f_equal].
  Qed.

  Lemma cl_log_div2' : forall n, cl_log (S n) = S (cl_log (div2 (S n))).
    intros.
    apply (Fix_eq _ lt lt_wf (fun _ => nat)).
    intuition.
    destruct x; [ reflexivity | repeat f_equal].
  Qed.

  Lemma fl_log_zero :  fl_log 0 = 0.
    apply (Fix_eq _ lt lt_wf (fun _ => nat)).
    intuition.
    destruct x; [ reflexivity | repeat f_equal].
  Qed.

  Lemma fl_log_div2 : forall n, fl_log (div2 n) + 1 = fl_log (S n).
    intros n.
    rewrite fl_log_div2'.
    intuition.
  Qed.

  Lemma fl_log_odd :
    forall n : nat, fl_log (n + n + 1) = (fl_log n) + 1.
    intro n.
    rewrite plus_comm; simpl.
    rewrite fl_log_div2'.
    rewrite double_div2.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

  Lemma fl_log_even :
    forall n : nat, fl_log ((n + 1) + (n + 1)) = (fl_log n) + 1.
    intro n.
    replace (n + 1 + (n + 1)) with (S (S (n + n))) ; [|omega].
    rewrite fl_log_div2'.
    rewrite odd_div2.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

  Lemma cl_log_odd :
    forall n, cl_log(n+n+1) = cl_log n + 1.
    intros.
    rewrite plus_comm; simpl.
    rewrite cl_log_div2'.
    rewrite odd_div2.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

  Lemma cl_log_even : 
    forall n,  cl_log (n+1) + 1 = cl_log (n + 1 + n + 1).
    intros.
    replace (n + 1 + n + 1) with (S (S (n+n))); [|omega].
    rewrite cl_log_div2'.
    replace (S (S (n+n))) with ((n+1)+(n+1)); [|omega].
    rewrite double_div2.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

End fl_log.
