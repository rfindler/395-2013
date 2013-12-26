Require Import braun util log.
Require Import Arith Arith.Even Arith.Div2.
Set Implicit Arguments.

Section size.
  Variable A : Set.

  Inductive SizeLinearR : (bin_tree A) -> nat -> nat -> Prop :=
    | SLR_mt :
        SizeLinearR (bt_mt A) 0 0
    | SLR_node :
        forall y s t s_sz s_time t_sz t_time,
          SizeLinearR s s_sz s_time ->
          SizeLinearR t t_sz t_time ->         
          SizeLinearR (bt_node y s t) (s_sz + t_sz + 1) (s_time + t_time + 1).
  Hint Constructors SizeLinearR.

  Theorem size_linear :
    forall bt,
      { sz | exists t, SizeLinearR bt sz t }.
  Proof.
    induction bt as [|y s IS t IT].

    exists 0. eauto.    
    destruct IS as [s_sz IS].
    destruct IT as [t_sz IT].
    exists (s_sz + t_sz + 1).
    destruct IS as [s_time IS].
    destruct IT as [t_time IT].
    exists (s_time + t_time + 1).
    eauto.
  Qed.

  Theorem SizeLinearR_time :
    forall bt n,
      Braun bt n ->
      SizeLinearR bt n n.
  Proof.
    induction bt as [|y s IS t IT]; intros n B;
    inversion_clear B; eauto.
  Qed.
  Hint Resolve SizeLinearR_time.

  Inductive DiffR : (bin_tree A) -> nat -> nat -> nat -> Prop :=
    | DR_mt :
        DiffR (bt_mt A) 0 0 0
    | DR_single :
        forall x,
          DiffR (bt_node x (bt_mt A) (bt_mt A)) 0 1 1
    | DR_one :
        forall x s t s_df s_time k,
          DiffR s k s_df s_time ->
          DiffR (bt_node x s t) (2 * k + 1) s_df (s_time+1)
    | DR_two :
        forall x s t t_df t_time k,
          DiffR t k t_df t_time ->
          DiffR (bt_node x s t) (2 * k + 2) t_df (t_time+1).
  Hint Constructors DiffR.

  Theorem diff_correct_ans :
    forall s m df t,
      DiffR s m df t ->
      (df = 0 \/ df = 1).
  Proof.
    intros s m df t DR.
    induction DR; auto.
  Qed.

  Theorem diff_correct_zero :
    forall s m,
      Braun s m ->
      forall dt,
        DiffR s m 0 dt ->
        exists lt, SizeLinearR s m lt.
  Proof.
    intros s m B.
    induction B; intros dt D.

    inversion_clear D.
    eauto.

    inversion D; clear D; subst.
    replace k with s_size in *; try omega.
    eapply IHB1 in H6.
    exists (s_size + s_size + 1).
    eapply SLR_node.
    eauto.
    replace (s_size + 0) with s_size; try omega.
    replace s_size with t_size; try omega.
    auto.

    replace k with t_size in *; try omega.
    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [EQ|EQ]; subst.

    eapply IHB2 in H6.
    exists (t_size + (t_size + 1) + 1).
    omega.

    eapply IHB2 in H6.
    exists ((t_size + 1) + t_size + 1).
    replace (t_size + (t_size + 0) + 2) with ((t_size + 1) + t_size + 1); try omega.
    eapply SLR_node; eauto.
  Qed.

  Theorem diff_correct_one :
    forall s m,
      Braun s m ->
      forall dt,
        DiffR s m 1 dt ->
        exists lt, SizeLinearR s (m+1) lt.
  Proof.
    intros s m B.
    induction B; intros dt D.

    inversion_clear D.

    inversion D; clear D; subst.
    symmetry in H4. apply plusone_ne_zero in H4. tauto.

    replace k with s_size in *; try omega.
    replace t_size with s_size in *; try omega.
    apply IHB1 in H6.
    destruct H6 as [lt SLRs].
    exists (lt + s_size + 1).
    replace (s_size + (s_size + 0) + 1 + 1) with ((s_size + 1) + s_size + 1); try omega.
    eapply SLR_node; eauto.

    replace k with t_size in *; try omega.
    assert (s_size = t_size \/ s_size = t_size + 1) as CASES; try omega.
    destruct CASES as [EQ|EQ]; subst.

    replace (t_size + (t_size + 0)) with (t_size + t_size) in H4; try omega.
    apply IHB2 in H6.
    destruct H6 as [lt SLRt].
    exists ((t_size+1) + lt + 1).
    replace (t_size + (t_size + 0) + 2 + 1) with
     ((t_size + 1) + (t_size + 1) + 1); try omega.
    eapply SLR_node; eauto.
  Qed.

  Theorem diff1 :
    forall bt m,
      { df | exists t, DiffR bt m df t }.
  Proof.
    induction bt as [|y s IS t IT]; intros m.

    (* XXX There's no reason to believe that m should be 0 here. So we
    could change DR_mt to be "forall m" *)
    
    admit.

    destruct m as [|m'].
    
    (* XXX There's no reason to believe that s and t are bt_mt. We
    could change DR_single to be "forall s t" *)

    admit.

    (* XXX Both of these changes seem wrong, because they mean that
    diff will return 0/1 when size != m or m+1 [unless we parameterize
    by Braunness?] and we should instead say either (a) some calls to
    diff are invalid [diff1 will be partial] or (b) its correctness
    relies on some property such as Braun-ness and m <= n <= m+1 *)

    destruct (even_odd_dec m') as [E | O].

    apply even_2n in E. 
    destruct E as [k E]; subst.
    destruct (IS k) as [s_df ISk].
    exists s_df.
    destruct ISk as [s_time ISk].
    exists (s_time+1).
    unfold double.
    replace (S (k + k)) with (2 * k + 1); try omega.
    eauto.

    apply odd_S2n in O.
    destruct O as [k O]; subst.
    destruct (IT k) as [t_df ITk].
    exists t_df.
    destruct ITk as [t_time ITk].
    exists (t_time+1).
    unfold double.
    replace (S (S (k + k))) with (2 * k + 2); try omega.
    eauto.
  Qed.

  (* XXX Maybe something like this will solve the problems above? But
  see size2 below *)

  Theorem diff2 :
    forall bt n,
      Braun bt n ->
      forall m,
        m <= n <= m + 1 ->
        { df | exists t, DiffR bt m df t }.
  Proof.
  Admitted.

  (* XXX diff running time *)

  Inductive SizeR : (bin_tree A) -> nat -> nat -> Prop :=
    | SR_mt :
        SizeR (bt_mt A) 0 0
    | SR_node :
        forall x s t m t_time s_df s_time,
          SizeR t m t_time ->
          DiffR s m s_df s_time ->
          SizeR (bt_node x s t) (1 + 2 * m + s_df) (s_time + t_time + 1).
  Hint Constructors SizeR.

  Theorem size :
    forall bt,
      { sz | exists t, SizeR bt sz t }.
  Proof.
    induction bt as [|y s IS t IT].
    eauto.
    clear IS.
    destruct IT as [m IT].
    destruct (diff1 s m) as [s_df DS].
    exists (1 + 2 * m + s_df).
    destruct IT as [t_time IT].
    destruct DS as [s_sime DS].
    eauto.
  Qed.

  Theorem size2 :
    forall bt n,
      Braun bt n ->
      { sz | exists t, SizeR bt sz t }.
  Proof.
    induction bt as [|y s IS t IT]; intros n B.
    eauto.
    clear IS.

    (* XXX We want to invert B to learn that t is Braun, but we cannot
    because we are in Set, but we can't get out of Set until /after/
    we use IT. Thus we're stuck. *)
  Admitted.

  (* XXX size running time *)

  (* XXX I think this is too strong because it says that you can
  derive one judgement from the other, rather than that they simply
  always agree *)

  Theorem size_correct1 :
    forall bt s,
      (exists t, SizeLinearR bt s t) <->
      (exists t, SizeR bt s t).
  Proof.
  Admitted.

  (* XXX I think this is too weak because it doesn't ensure the SLR or
  SR actually run, but I suppose we can conclude that from their
  decidability *)

  Theorem size_correct2 :
    forall bt ls s lt t,
      SizeLinearR bt ls lt ->
      SizeR bt s t ->
      s = ls.
  Proof.
  Admitted.

End size.

(*
Program Definition diff : 
  forall A n (b : braun_tree A n) (m : nat) (P : m <= n <= m+1), 
    C nat (if (eq_nat_dec m n) then (fl_log n) else (cl_log n)) :=
  fun A => fix diff n (b : braun_tree A n) : forall (m : nat) (P : m <= n <= m+1),
                                               C nat (if (eq_nat_dec m n)
                                                      then (fl_log n)
                                                      else (cl_log n)) :=
  match b as b in braun_tree _ n with
    | Empty => fun m P => ret 0
    | Node _ s1_size t1_size _ s1 t1 => 
      fun m P =>
        match m with
          | 0 => ++1; ret 1
          | S m' => 
            if even_odd_dec m
            then (zo <- diff t1_size t1 (div2 (m' - 1)) _;
                  ++1;
                  ret zo)
            else (zo <- diff s1_size s1 (div2 m') _;
                  ++1;
                  ret zo)
        end
  end.

Obligation 1.
inversion H; intuition.
Defined.

Obligation 2.
dispatch_if n o; intuition.
assert (s1_size = 0);[omega|];assert (t1_size = 0);[omega|].
subst;compute;reflexivity.
Defined.

Obligation 6.
dispatch_if n1 o1; dispatch_if o n.

(* case 1 *)
replace (s1_size+t1_size+ 1) with (t1_size+s1_size+1); [|omega].
apply braun_invariant_implies_fl_log_property.
inversion H; apply even_double in H3; unfold double in H3.
omega.

(* case 2 *)
inversion H as [n' EVEN].
apply even_double in EVEN.
unfold double in EVEN.
intuition.

(* case 3 *)
assert (m'=s1_size+t1_size);[omega|]; subst m'.
assert (t1_size = s1_size \/ s1_size = t1_size +1) as TWOCASES; [omega|];
inversion TWOCASES;subst.
  
(* case 3a *)
rewrite double_div2 in o1; intuition.
  
(* case 3b *)
replace (S (t1_size + 1 + t1_size)) with ((S t1_size) + (S t1_size)) in H; [|omega].
apply even_not_odd in H; intuition.

(* case 4 *) 
apply braun_invariant_implies_cl_log_property.
omega.
Defined.

Obligation 4.
dispatch_if n1 o1; dispatch_if n o.

(* case 1 *)
apply braun_invariant_implies_fl_log_property.
omega.

(* case 2 *)
destruct m';[inversion H;inversion H3|]. (* m' is not 0 *)
assert (even m');[inversion H; inversion H3; assumption|].
apply even_double in H2; unfold double in H2.
simpl in n1; rewrite minus_0r in n1.
intuition.

(* case 3 *)
assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; destruct SIZES1.

(* case 3a *)
subst t1_size.
rewrite n in H.
apply odd_not_even in H.
intuition.

(* case 3b *)
subst s1_size.
assert (m'-1 = t1_size + t1_size); [omega|].
assert (div2(m'-1) = t1_size); [rewrite H2;apply double_div2|].
intuition.

(* case 4 *)
assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; 
destruct SIZES1; subst s1_size.

(* case 4a *)
apply braun_invariant_implies_cl_log_property.
omega.

(* case 4b *)
assert (t1_size+t1_size+1 = S m' \/ t1_size+t1_size+1 = S (m'+1)) as SIZES2;
  [omega|]; destruct SIZES2; intuition.
rewrite <- H2 in H.
apply odd_not_even in H.
intuition.
Defined.

Obligation 5.
clear b Heq_b wildcard' s1 t1 A.

assert (s1_size = t1_size \/ s1_size = t1_size + 1) as SIZES1; [omega|]; clear l l0.
assert (S m' = s1_size + t1_size + 1 \/ S (m'+1) = s1_size + t1_size + 1) as SIZES2; [omega|]; clear H0 H1.
destruct SIZES1; destruct SIZES2; subst s1_size.

assert (m'=t1_size+t1_size); [omega|].
replace (div2 m') with t1_size; [omega|subst m'; rewrite double_div2; reflexivity].

rewrite plus_comm in H1.
simpl in H1.
rewrite plus_comm in H1.
simpl in H1.
inversion H1.
rewrite H2 in H.
apply even_not_odd in H.
intuition.

rewrite H1 in H.
replace (t1_size+1+t1_size+1) with ((t1_size+1)+(t1_size+1)) in H; [|omega].
apply even_not_odd in H.
intuition.

assert (m'=t1_size +t1_size); [omega|].
subst m'.
rewrite double_div2.
omega.

Defined.

Obligation 3.
clear b Heq_b wildcard' s1 t1 A.

assert (s1_size = t1_size \/ s1_size = t1_size + 1) as SIZES1; [omega|]; clear l l0.
assert (S m' = s1_size + t1_size + 1 \/ S (m'+1) = s1_size + t1_size + 1) as SIZES2; [omega|]; clear H0 H1.
destruct SIZES1; destruct SIZES2; subst s1_size.

rewrite H1 in H.
apply odd_not_even in H.
intuition.

assert (m'-1 = (t1_size-1)+(t1_size-1)); [omega|].
rewrite H0.
rewrite double_div2.
omega.

assert (m'-1 = t1_size+t1_size); [omega|].
rewrite H0.
rewrite double_div2.
omega.

assert (S m' = t1_size+t1_size+1); [omega|].
rewrite H0 in H.
apply odd_not_even in H.
intuition.
Defined.

Program Fixpoint size A (n:nat) (b : braun_tree A n) : C nat (sum_of_logs n) := 
  match b with 
    | Empty => ret 0
    | Node _ s_size t_size P s t =>
      (++1;
       zo <- diff s P ;
       (size_t <- size t ; 
        ret (1 + 2 * size_t + zo)))
  end.

Obligation 1.
clear Heq_b s t b.

dispatch_if n o; subst; rewrite plus_0_r.

rewrite <- sum_of_logs_odd.
rewrite fl_log_odd.
omega.

assert (t_size+1=s_size) as MN; [omega|].
subst s_size.
rewrite <- sum_of_logs_even.
rewrite <- cl_log_even.
omega.

Defined.
*)
