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

  Definition size := 0.
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
