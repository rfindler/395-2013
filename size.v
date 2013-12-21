Require Import braun util monad fl_log.
Set Implicit Arguments.

Program Fixpoint size_linear A n (b : braun_tree A n) : C nat n :=
  match b with
    | Empty => ret 0
    | Node y s_size t_size p s t =>
      (++ 1;
       s_sz <- size_linear s;
       t_sz <- size_linear t;
       ret (s_sz + t_sz + 1))
  end.

Require Import Arith Arith.Even Arith.Div2.

Program Definition diff : 
  forall A n (b : braun_tree A n) (m : nat) (P : m <= n <= m+1), 
    C nat (if (eq_nat_dec m n) then (fl_log n) else (cl_log n)) :=
  fun A => fix diff n (b : braun_tree A n) : forall (m : nat) (P : m <= n <= m+1),
                                               C nat (if (eq_nat_dec m n)
                                                      then (fl_log n)
                                                      else (cl_log n)) :=
  match b as b in braun_tree _ n with
    | Empty => fun m => fun P => ret 0
    | Node _ s1_size t1_size _ s1 t1 => 
      fun m =>
        match m with
          | 0 => fun P => ++1; ret 1
          | S m' => 
            match even_odd_dec m with
              | right H => 
                fun P => (zo <- diff s1_size s1 (div2 m') _;
                          ++1;
                          ret zo)
              | left H =>
                fun P => (zo <- diff t1_size t1 (div2 (m' - 1)) _;
                          ++1;
                          ret zo)
            end
        end
  end.

Obligation 1.
inversion H; clear.
destruct (eq_nat_dec 0 0); intuition.
Defined.

Obligation 2.
remember (match s1_size + t1_size + 1 as n return ({0 = n} + {0 <> n}) with
            | 0 => left eq_refl
            | S m => right (O_S m) end) as COND.
destruct COND; intuition.
inversion H0; intuition.
rewrite plus_comm in H2.
inversion H2.

assert (s1_size = 0);[omega|].
assert (t1_size = 0);[omega|].
subst.
simpl.
compute.
reflexivity.
Defined.

Obligation 4.

remember (match
             s1_size + t1_size + 1 as n return ({S m' = n} + {S m' <> n})
           with
             | 0 => right (not_eq_sym (O_S m'))
             | S m =>
               sumbool_rec
                 (fun _ : {m' = m} + {m' <> m} => {S m' = S m} + {S m' <> S m})
                 (fun a : m' = m => left (f_equal S a))
                 (fun b0 : m' <> m => right (not_eq_S m' m b0)) 
                 (eq_nat_dec m' m)
           end) as COND1.
remember (eq_nat_dec (div2 m') s1_size) as COND2.
destruct COND1; destruct COND2; clear HeqCOND1; clear HeqCOND2.


inversion H.
rewrite plus_comm in e; simpl in e; inversion e.
apply even_double in H3.
unfold double in H3.
assert (s1_size = t1_size); [omega|].
rewrite H4.
replace (t1_size + t1_size +1) with (S (t1_size+t1_size)); [|omega].
rewrite fl_log_div2'.
rewrite double_div2.
omega.

inversion H.

assert (m' = s1_size+t1_size \/ m' = s1_size+t1_size+1) as TWOCASES1; [omega|].
assert (t1_size = s1_size \/ s1_size = t1_size +1) as TWOCASES2; [omega|].
inversion TWOCASES1; inversion TWOCASES2; subst.

rewrite double_div2 in n.
intuition.

replace (t1_size + 1 + t1_size) with (t1_size+t1_size+1) in H3; [|omega].
apply odd_not_even in H3.
intuition.

apply odd_not_even in H3.
intuition.

replace (t1_size + 1 + t1_size + 1) with ((t1_size+1)+(t1_size+1)) in n;[|omega].
rewrite double_div2 in n.
intuition.



inversion H.
clear Heq_b Heq_anonymous s1 t1 b.

assert (m' = s1_size+t1_size \/ m'+1 = s1_size+t1_size) as TWOCASES1; [omega|].
assert (t1_size = s1_size \/ s1_size = t1_size+1) as TWOCASES2; [omega|].
inversion TWOCASES1; inversion TWOCASES2; clear TWOCASES1 TWOCASES2. 

subst s1_size n0.
subst t1_size.
rewrite <- H4 in n. intuition.

subst s1_size n0.
rewrite H5 in H4.
rewrite H4 in H3.
replace (t1_size + 1 + t1_size) with (t1_size+t1_size+1) in H3; [|omega].
apply odd_not_even in H3.
intuition.

subst s1_size n0.
subst t1_size.
assert (even (m'+1)).
rewrite H4.
apply double_is_even.
rewrite plus_comm in H2.
simpl in H2.
inversion H2.
apply (not_even_and_odd m') in H6; [|assumption].
intuition.


assert (m' = s1_size + s1_size).
rewrite <- e.
apply even_double; assumption.
intuition.  (* woah. no clue why that worked (or why the case is even true!). *)

assert (s1_size=t1_size \/ s1_size = t1_size +1) as TWOCASES; [omega|].
inversion TWOCASES; clear TWOCASES; subst s1_size.
replace (cl_log (t1_size + t1_size+1)) with (cl_log (S (t1_size + t1_size))).
replace (cl_log (S (t1_size + t1_size))) with (S (cl_log (div2 (S (t1_size + t1_size))))).
replace (div2 (S (t1_size+t1_size))) with t1_size.
rewrite plus_comm.
reflexivity.

rewrite (div2_with_odd_input t1_size).
reflexivity.

rewrite cl_log_div2'.
reflexivity.

replace (t1_size + t1_size+1) with (S (t1_size+t1_size)).
reflexivity.

omega.

assert (S m' = t1_size + 1 + t1_size + 1 \/ 
        t1_size + 1 + t1_size + 1 = S (m' + 1)) as TWOCASES2;
  [omega|].
inversion TWOCASES2; clear TWOCASES2; intuition.

replace (t1_size + 1 + t1_size + 1) with (S (S (t1_size+t1_size))); [|omega].
rewrite cl_log_div2'.

replace (S (S (t1_size+t1_size))) with ((S t1_size)+(S t1_size)); [|omega].
rewrite double_div2.
rewrite plus_comm.
simpl.
rewrite plus_comm.
reflexivity.

Defined.

Obligation 6.

remember (eq_nat_dec (div2 (m' - 1)) t1_size) as COND1.
remember (match
         s1_size + t1_size + 1 as n return ({S m' = n} + {S m' <> n})
       with
       | 0 => right (not_eq_sym (O_S m'))
       | S m =>
           sumbool_rec
             (fun _ : {m' = m} + {m' <> m} => {S m' = S m} + {S m' <> S m})
             (fun a : m' = m => left (f_equal S a))
             (fun b0 : m' <> m => right (not_eq_S m' m b0)) 
             (eq_nat_dec m' m)
       end) as COND2.
destruct COND1; destruct COND2; clear HeqCOND1; clear HeqCOND2.

assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; destruct SIZES1; subst s1_size.

rewrite fl_log_odd; reflexivity.

replace (t1_size+1+t1_size+1) with ((t1_size+1)+(t1_size+1));[|omega].
rewrite fl_log_even; reflexivity.

assert (s1_size+t1_size+1 = S m' \/ s1_size+t1_size+1 = S (m'+1)) as SIZES2; [omega|]; destruct SIZES2. 

intuition.

assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; destruct SIZES1.

subst t1_size.
subst s1_size.

assert (even (m'-1)).
inversion H.
inversion H4.
simpl.
rewrite minus_0r.
assumption.

replace (div2 (m'-1) + div2(m'-1) + 1) with m' in H2.
intuition.
apply even_double in H3.
unfold double in H3.
omega.

subst s1_size.
rewrite plus_comm in H2.
simpl in H2.
inversion H2.
assert (m' = t1_size + t1_size); [omega|].
clear Heq_anonymous.
rewrite H3 in H.
replace (S (t1_size+t1_size)) with (t1_size+t1_size+1) in H; [|omega].
assert False.
apply (odd_not_even t1_size); assumption.
intuition.

assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; destruct SIZES1.

subst t1_size.
clear Heq_anonymous.
rewrite e in H.
apply odd_not_even in H.
intuition.

subst s1_size.

assert (m'-1 = t1_size + t1_size); [omega|].
assert (div2(m'-1) = t1_size).
rewrite H2.
apply double_div2.
intuition.

assert (t1_size = s1_size \/ s1_size = t1_size+1) as SIZES1; [omega|]; destruct SIZES1; subst s1_size.

rewrite cl_log_odd; reflexivity.

clear Heq_b Heq_anonymous l l0.

assert (t1_size+t1_size+1 = S m' \/ t1_size+t1_size+1 = S (m'+1)) as SIZES2; [omega|]; destruct SIZES2;
intuition.

rewrite <- H2 in H.
apply odd_not_even in H.
intuition.
Defined.

Obligation 3.

clear Heq_anonymous b Heq_b wildcard' s1 t1 A.

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

Obligation 5.

clear Heq_anonymous b Heq_b wildcard' s1 t1 A.

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
    | Node _ _ _ P s t =>
      (++1;
       zo <- diff s P ;
       (size_t <- size t ; 
        ret (1 + 2 * size_t + zo)))
  end.

Obligation 1.
rename wildcard'0 into n.
rename wildcard'1 into m.
remember (eq_nat_dec m n) as COND.
destruct COND; clear HeqCOND Heq_b s t b; subst; rewrite plus_0_r.

rewrite <- sum_of_logs_odd.
rewrite fl_log_odd.
omega.

assert (m+1=n) as MN.
assert (m=n \/ m+1=n) as TWOCASES; [omega|]; destruct TWOCASES; omega.
subst n.
rewrite <- sum_of_logs_even.
rewrite <- cl_log_even.
omega.

Defined.
