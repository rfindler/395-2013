Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import util fl_log.

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

End sq_log.
