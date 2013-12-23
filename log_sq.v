Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import util log.

Set Implicit Arguments.

Section sq_log.

  Lemma fl_log_monotone :
    forall n, fl_log n <= fl_log (S n).
    apply (well_founded_ind
             lt_wf
             (fun n => fl_log n <= fl_log (S n))).
    intros.
    destruct x.
    compute. omega.
    rewrite <- fl_log_div2.
    rewrite <- fl_log_div2.
    rewrite plus_comm.
    unfold plus at 1.
    rewrite plus_comm.
    unfold plus.
    apply le_n_S.
    assert (even x \/ odd x) as EO; [apply even_or_odd | inversion EO; clear EO].
    rewrite even_div2;[constructor|assumption].
    rewrite <- odd_div2;[|assumption].
    apply H.
    apply lt_div2'.
  Qed.

  Lemma cl_log_monotone :
    forall n, cl_log n <= cl_log (S n).
    apply (well_founded_ind
             lt_wf
             (fun n => cl_log n <= cl_log (S n))).
    intros.
    destruct x.
    compute. omega.
    rewrite cl_log_div2'.
    rewrite cl_log_div2'.
    apply le_n_S.
    assert (even (S x) \/ odd (S x)) as EO; [apply even_or_odd | inversion EO; clear EO].
    rewrite even_div2;[constructor|assumption].
    rewrite <- (odd_div2 (S x));[|assumption].
    apply H.
    apply lt_div2''.
  Qed.

  Lemma fl_log_leq_cl_log : 
    forall n, fl_log n <= cl_log n.
    apply (well_founded_ind 
             lt_wf 
             (fun n => fl_log n <= cl_log n)).
    intros.
    destruct x.
    compute. omega.
    rewrite fl_log_div2'.
    rewrite cl_log_div2'.
    apply le_n_S.
    apply (le_trans (fl_log (div2 x))
                    (fl_log (div2 (S x)))
                    (cl_log (div2 (S x)))).

    assert (even x \/ odd x) as EO; [apply even_or_odd | inversion EO; clear EO].
    rewrite even_div2; [|assumption].
    omega.

    rewrite <- odd_div2; [|assumption].
    apply fl_log_monotone.

    apply H.
    apply lt_div2''.
  Qed.

  Lemma le_plus_left :
    forall n n' m, n <= n' -> n+m <= n'+m.
    induction m.
    intros.
    omega.
    intros.
    rewrite plus_comm.
    simpl.
    replace (n' + S m) with (S (n' + m)); [|omega].
    apply le_n_S.
    replace (m+n) with (n+m); [|omega].
    apply IHm.
    assumption.
  Qed.

  Lemma le_plus_right:
    forall n n' m, n <= n' -> m+n <= m+n'.
    intros.
    rewrite plus_comm.
    replace (m+n') with (n'+m);[|omega].
    apply le_plus_left; assumption.
  Qed.

  Lemma plus_one_sq : forall n, (n+1)*(n+1) = n*n+2*n+1.
    intros n.
    rewrite mult_plus_distr_r.
    rewrite mult_plus_distr_l.
    omega.
    Qed.

  Lemma le_add_right : forall n m o, n <= m -> n <= m + o.
    induction o.
    intros.
    rewrite plus_0_r; assumption.
    intros.
    replace (m+S o) with (S (m+o));[|omega].
    constructor.
    apply IHo.
    assumption.
  Qed.

  Lemma le_mult_left : forall m n o, m <= n -> m*o <= n*o.
    intros.
    induction o.
    omega.
    rewrite mult_comm.
    replace (n*(S o)) with ((S o)*n);[|apply mult_comm].
    simpl.
    rewrite mult_comm.
    replace (o*n) with (n*o); [|apply mult_comm].
    omega.
  Qed.

  Lemma le_mult_right : forall m n o, m <= n -> o*m <= o*n.
    intros.
    rewrite mult_comm.
    replace (o*n) with (n*o);[|apply mult_comm].
    apply le_mult_left.
    assumption.
  Qed.

  Lemma cl_log_sq_S : forall n, (cl_log n * cl_log n) <= (cl_log (S n) * cl_log (S n)).
    intros.
    apply (le_trans (cl_log n * cl_log n)
                    (cl_log (S n) * cl_log n)
                    (cl_log (S n) * cl_log (S n))).
    apply le_mult_left.
    apply cl_log_monotone.
    apply le_mult_right.
    apply cl_log_monotone.
  Qed.


  Lemma upper_bound_sum_of_logs_even :
    forall x,
      (forall y : nat, y < S x -> sum_of_logs y <= cl_log y * cl_log y) ->
      (even (S x)) -> 
      sum_of_logs (S x) <=
      cl_log (div2 (S x)) * cl_log (div2 (S x)) + 2 * cl_log (div2 (S x)) + 1.
    intros x IND EVEN.

    replace (sum_of_logs (S x)) with (sum_of_logs (div2 (S x) + div2 (S x))).
    inversion EVEN.
    replace (div2 (S x)) with (S (div2 x)).
    replace (S (div2 x) + S (div2 x)) with (div2 x + 1 + div2 x + 1);[|omega].
    rewrite <- sum_of_logs_even.

    rewrite <- cl_log_even.

    replace (cl_log (S (div2 x)) * cl_log (S (div2 x)) + 2 * cl_log (S (div2 x)) + 1)
             with
             ((cl_log (div2 x+1) + 1) +
              (cl_log (S (div2 x)) * cl_log (S (div2 x)) + cl_log (S (div2 x))));
      [|replace (S (div2 x)) with (div2 x + 1); [|omega] ; omega].

    apply le_plus_right.

    apply (le_trans (sum_of_logs (div2 x))
                    (cl_log (div2 x) * cl_log (div2 x))
                    (cl_log (S (div2 x)) * cl_log (S (div2 x)) + cl_log (S (div2 x)))).
    apply IND.
    apply lt_div2'.
    
    replace (cl_log (S (div2 x)) * cl_log (S (div2 x)) + cl_log (S (div2 x)))
            with
            (cl_log (S (div2 x)) * cl_log (S (div2 x)) + (cl_log (S (div2 x))));[|omega].

    apply (le_add_right (cl_log (S (div2 x)))).

    apply cl_log_sq_S.

    rewrite odd_div2; [reflexivity|assumption].

    replace (div2 (S x) + div2 (S x)) with (double (div2 (S x))); [|unfold double;reflexivity].
    rewrite <- (even_double (S x)); [|assumption].
    reflexivity.
    Qed.

  Lemma upper_bound_sum_of_logs_odd : 
    forall x, 
      (forall y : nat, y < S x -> sum_of_logs y <= cl_log y * cl_log y) -> 
      (odd (S x)) -> 
      sum_of_logs (S x) <=
      cl_log (div2 (S x)) * cl_log (div2 (S x)) + 2 * cl_log (div2 (S x)) + 1.
    intros x IND ODD.
    inversion ODD as [junk EVEN junk']; clear junk junk'.
    assert (S x = div2 x + div2 x + 1).
    replace (div2 x + div2 x) with (double (div2 x));[|unfold double; reflexivity].
    rewrite <- even_double; [|assumption].
    omega.
    replace (sum_of_logs (S x)) with (sum_of_logs(div2 x+div2 x+1));[|rewrite H;reflexivity].

    rewrite <- sum_of_logs_odd.

    rewrite fl_log_odd.

    replace (cl_log (div2 (S x)) * cl_log (div2 (S x)) + 2 * cl_log (div2 (S x)) + 1)
    with ((cl_log(div2 (S x)) + 1) +
          cl_log (div2 (S x)) * cl_log (div2 (S x)) + cl_log (div2 (S x)));[|omega].

    apply (le_add_right (cl_log (div2 (S x)))).

    replace (div2 (S x)) with (div2 x); [|apply even_div2;assumption].

    assert (fl_log (div2 x) <= cl_log (div2 x)) as LEFTPIECE; [apply fl_log_leq_cl_log|].

    assert (sum_of_logs (div2 x) <= cl_log (div2 x) * cl_log (div2 x)) as RIGHTPIECE;
      [apply IND;apply lt_div2'|].

    omega.
  Qed.
      
  Theorem upper_bound_sum_of_logs :
    forall n, sum_of_logs n <= cl_log n * cl_log n.
    apply (well_founded_ind 
             lt_wf 
             (fun n => sum_of_logs n <= cl_log n * cl_log n)).
    intros.
    destruct x.
    compute. constructor.

    rewrite cl_log_div2'.
    replace ((S (cl_log (div2 (S x)))) * (S (cl_log (div2 (S x)))))
    with ((cl_log (div2 (S x))+1) * ((cl_log (div2 (S x)))+1)).
    rewrite plus_one_sq.

    assert (even (S x) \/ odd (S x)) as EVENODD; [apply even_or_odd|destruct EVENODD].
    apply upper_bound_sum_of_logs_even; repeat assumption.
    apply upper_bound_sum_of_logs_odd; repeat assumption.
    replace (cl_log (div2 (S x)) + 1) with (S (cl_log (div2 (S x)))); [|omega].
    reflexivity.
  Qed.

End sq_log.
