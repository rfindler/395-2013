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

  Program Fixpoint sum_of_logs n {wf lt n} : nat :=
    match n with
      | 0 => 0
      | S n' =>
        match even_odd_dec n' with
          | right H =>
            cl_log n + sum_of_logs (proj1_sig (odd_S2n n' H))
          | left H =>
            fl_log n + sum_of_logs (proj1_sig (even_2n n' H))
        end
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

  Example sum_of_logs_ex :
    map sum_of_logs
        [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18;
         19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31; 32; 33; 34; 35;
         36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46; 47; 48; 49; 50; 51; 52;
         53; 54; 55; 56; 57; 58; 59; 60; 61; 62; 63] =
    [0; 1; 2; 3; 4; 4; 5; 6; 7; 7; 8; 7; 8; 8; 9; 10; 11; 11; 12; 11; 12; 12; 
     13; 11; 12; 12; 13; 12; 13; 13; 14; 15; 16; 16; 17; 16; 17; 17; 18; 16; 17;
     17; 18; 17; 18; 18; 19; 16; 17; 17; 18; 17; 18; 18; 19; 17; 18; 18; 19; 18; 
     19; 19; 20; 21]%list.
  compute;reflexivity.
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

  Lemma sum_of_logs_even :
    forall m,
      cl_log (m + 1 + m + 1) + sum_of_logs m = sum_of_logs (m + 1 + m + 1).
    intros.
    replace (m+1+m+1) with (S (S (m+m)));[|omega].
    replace (m+1) with (S m); [|omega].
    symmetry.
    (* apply (Fix_eq _ lt lt_wf (fun _ => nat)).  *)
    Admitted.

  Lemma sum_of_logs_odd :
    forall n,
      fl_log (n+n+1) + sum_of_logs n = sum_of_logs (n + n + 1).
    intros.
    replace (n+n+1) with (S (n+n)); [|omega].
  (* apply (Fix_eq _ lt lt_wf (fun _ => nat)). *)
  Admitted.

End fl_log.
