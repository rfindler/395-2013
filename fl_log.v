Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax List.
Require Import util.

Set Implicit Arguments.

Section fl_log.

  (* fl_log(n) = floor(log_2(n+1)) *)
  Program Fixpoint fl_log n {wf lt n} : nat :=
    match n with
      | 0 => 0
      | S n' => S (fl_log (div2 n'))
    end.

  (* cl_log(n) = ceiling(log_2(n+1)) 
     which is the same as Racket's 'integer-length' *)
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
            cl_log n + sum_of_logs (div2 n')
          | left H =>
            fl_log n + sum_of_logs (div2 n')
        end
    end.
  
  Example fl_log_ex :
    map fl_log
        [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
      = [0;1;1;2;2;2;2;3;3;3;3; 3; 3; 3; 3; 4].
  compute; reflexivity.
  Qed.

  Example cl_log_ex :
    map cl_log
        [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
      = [0;1;2;2;3;3;3;3;4;4;4; 4; 4; 4; 4; 4].
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
    rewrite div2_with_odd_argument.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

  Lemma cl_log_odd :
    forall n, cl_log(n+n+1) = cl_log n + 1.
    intros.
    rewrite plus_comm; simpl.
    rewrite cl_log_div2'.
    rewrite div2_with_odd_argument.
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
    WfExtensionality.unfold_sub sum_of_logs (sum_of_logs (S (S (m + m)))).
    destruct (even_odd_dec (S (m + m))).

    inversion e.
    rewrite <- H in H0.
    assert (even n); [rewrite H; eapply double_even;
                      rewrite double_div2; unfold double; reflexivity|].
    apply not_even_and_odd in H1. contradiction. assumption.

    fold_sub sum_of_logs.
    clear o.
    replace (match m + m with
               | 0 => 0
               | S n' => S (div2 n')
               end)
            with m.
    reflexivity.
    induction m. simpl. reflexivity.
    replace (S m + S m) with (S (S (m + m))); [|omega].
    rewrite div2_with_odd_input. reflexivity.
  Qed.

  Lemma sum_of_logs_odd :
    forall n,
      fl_log (n+n+1) + sum_of_logs n = sum_of_logs (n + n + 1).
    intros.
    replace (n+n+1) with (S (n+n)); [|omega].
    WfExtensionality.unfold_sub sum_of_logs (sum_of_logs (S (n + n))).
    destruct (even_odd_dec (n + n)).
    
    fold_sub sum_of_logs.
    rewrite double_div2.
    reflexivity.

    assert (even (n + n)); [apply double_is_even|].
    apply not_even_and_odd in H.
    contradiction.
    assumption.
  Qed.

  Lemma braun_invariant_implies_fl_log_property : 
    forall s_size t_size,
      t_size <= s_size <= t_size + 1 ->
      fl_log t_size + 1 = fl_log (s_size + t_size + 1).

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

  Lemma braun_invariant_implies_cl_log_property:
    forall s1_size t1_size,
      t1_size <= s1_size <= t1_size + 1 ->
      cl_log s1_size + 1 = cl_log (s1_size + t1_size + 1).

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


End fl_log.
