Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax List.
Require Import Braun.common.util.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Lexicographic_Product.

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

Lemma cl_log_zero :
  cl_log 0 = 0.
Proof.
  apply (Fix_eq _ lt lt_wf (fun _ => nat)).
  intuition.
  destruct x; [ reflexivity | repeat f_equal].
Qed.
Hint Rewrite cl_log_zero.

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

Lemma div2_le:
  forall n,
    div2 n <= n.
Proof.
  induction n as [|n].
  simpl. auto.

  apply NPeano.div2_decr.
  auto.
Qed.

Lemma ind_0_div2 :
  forall P:nat -> Prop,
    P 0 -> (forall n, P (div2 n) -> P (S n)) -> forall n, P n.
Proof.
  intros P P0 I.
  apply (well_founded_ind lt_wf P).
  intros n IH.
  destruct n as [|n].
  auto.
  apply I.
  apply IH.
  unfold lt.
  apply le_n_S.
  apply div2_le.
Qed.

Lemma fl_log_decr:
  forall x,
    fl_log x <= x.
Proof.
  apply ind_0_div2.
  
  rewrite fl_log_zero.
  auto.

  intros n.
  rewrite <- fl_log_div2.
  intros LE.
  rewrite plus_comm. simpl.
  apply le_n_S.
  eapply le_trans.
  apply LE.
  apply div2_le.
Qed.

Lemma fl_log_monotone:
  forall x y,
    x <= y ->
    fl_log x <= fl_log y.
Proof.
  apply (ind_0_div2 (fun x => forall y : nat, x <= y -> fl_log x <= fl_log y)).

  intros y LE. 
  rewrite fl_log_zero.
  apply le_0_n.

  intros n IH y LE.
  rewrite <- fl_log_div2.
  destruct y as [|y].
  omega.
  assert (n <= y) as LE'; try omega.
  clear LE.
  rewrite <- fl_log_div2.
  rewrite plus_comm. simpl.
  rewrite plus_comm. simpl.
  apply le_n_S.
  apply IH.
  apply div2_monotone.
  auto.
Qed.

Lemma cl_log_monotone:
  forall x y,
    x <= y ->
    cl_log x <= cl_log y.
Proof.
  intros [|n] y LE.
  
  rewrite cl_log_zero.
  apply le_0_n.

  rewrite <- fl_log_cl_log_relationship.
  destruct y as [|y].
  omega.
  rewrite <- fl_log_cl_log_relationship.
  assert (n <= y) as LE'; try omega.
  apply le_n_S.
  apply fl_log_monotone.
  auto.
Qed.

Lemma S_cl_log_doubles : 
  forall n, S (cl_log (S n)) = cl_log (S n + S n).
Proof.
  intros.
  rewrite <- (double_div2 (S n)) at 1.
  replace (S n + S n) with (S (n+S n)) at 1;[|omega].
  rewrite <- cl_log_div2'.
  replace (S (n+S n)) with (S n + S n);omega.
Qed.

Lemma cl_log_product : forall n m, cl_log (n*m) <= 2*cl_log n + 2*cl_log m.
Proof.
  intros.
  apply (lt_wf_double_ind (fun n m => cl_log (n*m) <= 2*cl_log n + 2*cl_log m)).
  clear.
  intros.
  destruct n.
  rewrite mult_0_l.
  rewrite cl_log_zero.
  omega.
  destruct m.
  rewrite mult_0_r.
  rewrite cl_log_zero.
  omega.
  destruct (even_odd_dec n).
  destruct (even_odd_dec m).
  destruct n. rewrite mult_1_l. omega.
  destruct m. rewrite mult_1_r. omega.
  apply (le_trans (cl_log (S (S n) * S (S m)))
                  (cl_log (div2 (S (S n)) * div2 (S (S m))) + 4)).
  replace (div2 (S (S n))) with (div2 (S n));[|apply even_div2; auto].
  replace (div2 (S (S m))) with (div2 (S m));[|apply even_div2; auto].
  rewrite <- even_div_product; auto.
  replace ((S n) * div2 (S m)) with (div2 (S m) * (S n));[|rewrite mult_comm;auto].
  rewrite <- even_div_product; auto.
  destruct n.
  inversion e.
  inversion H2.
  destruct m.
  inversion e0.
  inversion H2.
  replace (S (S n)) with (n+2) at 2;[|omega].
  replace (S (S m)) with (m+2) at 2;[|omega].
  rewrite mult_plus_distr_r;
    repeat (rewrite mult_plus_distr_l);
    rewrite plus_assoc.
  replace (m * n + m * 2 + 2 * n + 2 * 2)
  with (S (S (S (S (m * n + m * 2 + 2 * n)))));[|omega].
  unfold div2 at 2; fold div2.
  replace (cl_log (div2 (S (S (div2 (m * n + m * 2 + 2 * n))))) + 4)
  with (S (S (S (S (cl_log (div2 (S (S (div2 (m * n + m * 2 + 2 * n))))))))));[|omega].
  rewrite <- cl_log_div2'.
  replace (S (S (div2 (m * n + m * 2 + 2 * n))))
  with (div2 (S (S (S (S (m * n + m * 2 + 2 * n))))));[|unfold div2;auto].
  rewrite <- cl_log_div2'.
  rewrite S_cl_log_doubles.
  replace (S (S (S (S (m * n + m * 2 + 2 * n)))) +
           S (S (S (S (m * n + m * 2 + 2 * n)))))
  with (S ((S (S (S (m * n + m * 2 + 2 * n)))) +
           S (S (S (S (m * n + m * 2 + 2 * n))))));[|omega].
  rewrite S_cl_log_doubles.
  apply cl_log_monotone.
  replace (S (S (S n))) with (n+3);[|omega].
  replace (S (S (S m))) with (m+3);[|omega].
  rewrite mult_plus_distr_r;
    repeat (rewrite mult_plus_distr_l);
    rewrite plus_assoc.
  rewrite mult_comm at 1.
  remember (m*n) as l.
  omega.
  repeat rewrite cl_log_div2'.
  replace ( 2 * S (cl_log (div2 (S (S n)))) + 2 * S (cl_log (div2 (S (S m)))))
  with ( 2 * (cl_log (div2 (S (S n)))) + 2 * (cl_log (div2 (S (S m)))) + 4);[|omega].
  apply plus_le_compat; auto.
  replace (S n) with (n + 1); try omega.
  replace (S m) with (m + 1); try omega.
  assert (((n+1)*(m+1)) = (n*m + m + n + 1)); try omega.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  omega.
  rewrite H1.
  replace (n*m+m+n+1) with (S(n*m+m+n));[|omega].
  rewrite cl_log_div2'.
  replace (S(n*m+m+n)) with (n*m+m+n+1);[|omega].
  rewrite <- H1.
  rewrite mult_comm.
  rewrite even_div_product;[|apply odd_even_plus; auto; repeat constructor].
  apply (le_trans (S (cl_log (div2 (m + 1) * (n + 1))))
                  (2*cl_log(div2(m+1)) + 2*cl_log(n+1) + 1)).
  replace (S (cl_log (div2 (m + 1) * (n + 1))))
  with (cl_log (div2 (m + 1) * (n + 1)) +1);[|omega].
  apply plus_le_compat;auto.
  rewrite mult_comm.
  replace ( 2 * cl_log (div2 (m + 1)) + 2 * cl_log (n + 1))
  with  (2 * cl_log (n + 1) + 2 * cl_log (div2 (m + 1)));[|apply plus_comm].
  replace (n+1) with (S n); [auto|omega].
  replace (m+1) with (S m);[auto|omega].
  replace (cl_log (S m)) with (S (cl_log (div2 (S m))));[|
                                                        apply eq_sym;
                                                          apply cl_log_div2']; omega.
   replace (S n) with (n + 1); try omega.
  replace (S m) with (m + 1); try omega.
  assert (((n+1)*(m+1)) = (n*m + m + n + 1)); try omega.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_l.
  omega.
  rewrite H1.
  replace (n*m+m+n+1) with (S(n*m+m+n));[|omega].
  rewrite cl_log_div2'.
  replace (S(n*m+m+n)) with (n*m+m+n+1);[|omega].
  rewrite <- H1.
  rewrite even_div_product;[|apply odd_even_plus; auto; repeat constructor].
  apply (le_trans (S (cl_log (div2 (n + 1) * (m + 1))))
                  (2*cl_log(div2(n+1)) + 2*cl_log(m+1) + 1)).
  replace  (S (cl_log ((div2 (n+1)) * (m+1)))) with  (cl_log ((div2 (n+1)) * (m+1)) + 1).
  apply plus_le_compat; auto.
  omega.
  replace (n+1) with (S n);[|omega].
  rewrite cl_log_div2'.
  omega.
Qed.

Lemma cl_log_square_four :
  forall n, cl_log (n * n) <= 4 * cl_log n.
Proof.
  intros.
  eapply le_trans.
  apply cl_log_product.
  omega.
Qed.

Definition monotone (f : nat -> nat) := forall n m, n<=m -> f n <= f m.

Theorem log_prod_time :
  forall (n k:nat) (f g : nat -> nat),
    monotone g ->
    f 0 = k /\ (forall n, f (S n) = f (div2 (S n)) + g (S n)) ->
    f n <= (cl_log n)*(g n) + k.
Proof.
  intros n k f g Mono_g H.
  destruct H.
  apply (well_founded_ind
           lt_wf
           (fun n =>  f n <= cl_log n * g n + k)).
  clear n.
  intros n IH.
  destruct n.
  rewrite H.
  rewrite cl_log_zero. omega.
  rewrite H0.
  rewrite cl_log_div2'.
  replace (S (cl_log (div2 (S n)))) with ((cl_log (div2 (S n)))+1);[|omega].
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  rewrite <- plus_assoc.
  replace (g (S n) + k) with (k + g (S n));[|omega].
  rewrite plus_assoc.
  apply plus_le_compat; auto.
  eapply le_trans.
  apply IH.
  apply lt_div2. omega.
  apply plus_le_compat; auto.
  apply mult_le_compat.
  auto.
  apply Mono_g.
  assert (div2 (S n) < S n).
  auto. omega.
Qed.

Theorem log_prod_time2 :
  forall (n m k:nat) (f g : nat -> nat -> nat),
    (forall m, monotone (fun n => g n m)) ->
    (forall m, f 0 m = k) /\ (forall n m, f (S n) m = f (div2 (S n)) m + g (S n) m) ->
    f n m <= (cl_log n)*(g n m) + k.
  intros n m k f g Mono_g H.
  destruct H.
  apply (well_founded_ind
           lt_wf
           (fun n => forall m, f n m <= (cl_log n)*(g n m) + k)).
  clear n m.
  intros n IH.
  intros m.
  destruct n.
  rewrite H.
  rewrite cl_log_zero. omega.
  rewrite H0.
  rewrite cl_log_div2'.
  replace (S (cl_log (div2 (S n)))) with ((cl_log (div2 (S n)))+1);[|omega].
  rewrite mult_plus_distr_r.
  rewrite mult_1_l.
  rewrite <- plus_assoc.
  replace (g (S n) m + k) with (k + g (S n) m);[|omega].
  rewrite plus_assoc.
  apply plus_le_compat; auto.
  eapply le_trans.
  apply IH.
  apply lt_div2. omega.
  apply plus_le_compat; auto.
  apply mult_le_compat.
  auto.
  apply Mono_g.
  assert (div2 (S n) < S n).
  auto. omega.
Qed.
