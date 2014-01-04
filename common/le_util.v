Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Braun.common.util Braun.common.log.

Set Implicit Arguments.

Lemma fl_log_monotone :
  forall n,
    fl_log n <= fl_log (S n).
Proof.
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
  forall n,
    cl_log n <= cl_log (S n).
Proof.
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
  forall n,
    fl_log n <= cl_log n.
Proof.
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
  forall n n' m,
    n <= n' -> n+m <= n'+m.
Proof.
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
  forall n n' m,
    n <= n' -> m+n <= m+n'.
Proof.
  intros.
  rewrite plus_comm.
  replace (m+n') with (n'+m);[|omega].
  apply le_plus_left; assumption.
Qed.

Lemma plus_one_sq : 
  forall n, 
    (n+1)*(n+1) = n*n+2*n+1.
Proof.
  intros n.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_l.
  omega.
Qed.

Lemma le_add_right :
  forall n m o, 
    n <= m -> n <= m + o.
Proof.
  induction o.
  intros.
  rewrite plus_0_r; assumption.
  intros.
  replace (m+S o) with (S (m+o));[|omega].
  constructor.
  apply IHo.
  assumption.
Qed.

Lemma le_mult_left :
  forall m n o,
    m <= n -> m*o <= n*o.
Proof.
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

Lemma le_mult_right : 
  forall m n o, m <= n -> o*m <= o*n.
Proof.
  intros.
  rewrite mult_comm.
  replace (o*n) with (n*o);[|apply mult_comm].
  apply le_mult_left.
  assumption.
Qed.

Lemma le_pieces_le_prod :
  forall a b c d,
    a <= b -> c <= d -> a*c <= b*d.
Proof.
  intros.

  induction d.
  replace c with 0;[|omega].
  rewrite mult_comm; apply le_0_n.

  inversion H0.
  apply le_mult_left.
  assumption.

  apply IHd in H2.

  apply (le_trans (a * c)
                  (b * d)
                  (b * S d)).
  assumption.

  rewrite mult_comm.
  replace (b * S d) with (S d * b);[|apply mult_comm].

  simpl.
  omega.
Qed.

Lemma div2_mult :
  forall n m, 
    m*div2(n)+m*div2(n) <= m*n.
Proof.
  induction m.
  simpl;reflexivity.

  unfold mult;fold mult.

  replace (div2 n + m * div2 n + (div2 n + m * div2 n))
  with (div2 n + div2 n + (m * div2 n + m * div2 n));[|omega].

  apply (le_trans (div2 n + div2 n + (m * div2 n + m * div2 n))
                  (div2 n + div2 n + m * n)
                  (n + m * n)).
  apply le_plus_right.
  apply IHm.

  apply le_plus_left.

  apply div2_doubled_le_n.
Qed.
