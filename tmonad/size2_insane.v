(* This version aims be as faithful as possible to Chris's version of
   the diff function. Specifically, Chris's text suggests that he
   considers the first input to 'diff' to be always a Braun trees so
   this insists on that in the type, and this function also has (as
   close as we can get to) the same four cases as Chris's does.  *)

Require Import Braun.common.braun Braun.common.log.
Require Import Braun.common.util Braun.common.log_sq.  
Require Import Braun.tmonad.monad Braun.tmonad.insert.  
Require Import Coq.Program.Wf Arith.Even Arith.Div2 Arith.

Set Implicit Arguments.

Program Fixpoint diff A 
        (sb : { b : @bin_tree A | exists bn, Braun b bn } )
        (sm : { m : nat | Braun (proj1_sig sb) m \/ Braun (proj1_sig sb) (m+1) } )
        {wf lt sm} 
: {! sn !:! { n | n = 0 \/ n = 1 } !<! c !>!
     (forall bn, Braun sb bn -> bn = sm + sn)
     /\ c = fl_log sm + sn !} :=
  match sb, sm with
    | bt_mt                , 0 => <== (exist _ 0 _)
    | bt_mt                , S _ => False_rect _ _
    | bt_node x    _      _, 0 => ++; <== (exist _ 1 _)
    | bt_node x    s      t, (S m') =>
      if (even_odd_dec sm)
      then
        let st := (exist _ t _) in
        let stm := (exist _ (div2 (m'-1)) _) in
        o <- diff st stm;
        ++; <== o
      else 
        let ss := (exist _ s _) in
        let ssm := (exist _ (div2 m') _) in
        o <- diff ss ssm;
        ++; <== o
  end.

Next Obligation.
  rename H0 into bn.
  rename H1 into Bb.
  rename H into Bsm.
  simpl in Bsm.
  destruct Bsm as [Bsm|Bsm]; [|invclr Bsm].

  split; auto.
  intros bn' Bb'. invclr Bb'. auto.
Qed.

Next Obligation.
  rename wildcard' into m'.
  clear diff.
  rename H1 into Bb.
  rename H into Bsm.
  rename H0 into Bn.

  destruct Bsm as [Bsm|Bsm]; invclr Bsm.
Defined.

Next Obligation.
  rename H0 into bn.
  rename H1 into Bb.
  rename H into Bsm.
  rename wildcard' into s.
  rename wildcard'0 into t.
  split; auto.
  intros bn' Bb'.
  destruct Bsm as [Bsm|Bsm].
  invclr Bsm; omega.
  eapply same_tree_same_size; eauto.
Qed.

Next Obligation.
  rename H2 into Bb.
  invclr Bb; eauto.
Qed.

Next Obligation.
  rename H1 into bn.
  rename H into E.
  rename H2 into Bb.
  rename H0 into Bsm.
  clear bn Bb.
  clear diff.
  apply even_2n in E.
  destruct E as [p EQp].
  unfold double in EQp.
  destruct Bsm as [Bsm|Bsm]; invclr Bsm;
  rename H3 into BP;
    rename H4 into Bs;
    rename H5 into Bt;
    rename H2 into EQ.

  replace s_size with (t_size+1) in *; try omega.
  rewrite EQp in *.
  replace p with (t_size + 1) in *; try omega.
  clear p EQ s_size.
  replace m' with (t_size + 1 + t_size) in *; try omega.
  replace (t_size + 1 + t_size - 1) with (t_size + t_size); try omega.
  rewrite double_div2. auto.

  replace s_size with t_size in *; try omega.
  replace p with t_size in *; try omega.
  clear p s_size.
  replace m' with (t_size + t_size - 1) in *; try omega.

  assert (t_size = 0 \/ t_size = (div2 (t_size + t_size - 1 - 1) + 1)) as CASES.
  clear A x s t m' EQp BP Bs Bt EQ.
  destruct t_size; try omega.
  replace (S t_size + S t_size - 1 - 1) with (t_size + t_size); try omega.
  rewrite double_div2. omega.

  destruct CASES as [EQ'|EQ']; [rewrite EQ' in *|rewrite <- EQ']; auto.
Qed.

Obligations.

(* At this point, it is clearly do-able... but I don't think it is
worth it. *)

Admit Obligations.

Recursive Extraction diff.

Print diff_func_obligation_3.

Program Fixpoint size A (b : @bin_tree A) 
: {! n !:! nat !<! c !>! 
     forall m,
       (Braun b m -> (n = m /\ c = sum_of_logs n)) !} := 
  match b with 
    | bt_mt => <== 0
    | bt_node _ s t =>
      (++;
       m <- size t ; 
       zo <- diff s m;
       <== (1 + 2 * m + zo))
  end.

Next Obligation.
Proof.
  inversion H.
  constructor;auto.
Qed.  

Next Obligation.
  admit.
Qed.

Next Obligation.
  admit.
Qed.

Next Obligation.
Proof.
  invclr H1.
  clear wildcard'.
  rename H5 into IBt.
  rename H0 into IBt'.
  rename H3 into IBs.
  clear H.
  rename H6 into EQzo.
  rename H8 into BP.
  rename H10 into Bs.
  rename H11 into Bt.
  destruct (IBt _ Bt). subst.
  destruct (IBt' _ Bt). subst.
  clear IBt IBt' Bt H.
  apply IBs in Bs. subst. clear IBs.
  split. omega.
  destruct EQzo; subst.

  replace (S (t_size + (t_size + 0) + 0)) with (t_size+t_size+1);[|omega].
  rewrite <- sum_of_logs_odd.
  rewrite fl_log_odd.
  omega.

  replace (S (t_size + (t_size + 0) + 1)) with (t_size + 1 + t_size + 1);[|omega].
  rewrite <- sum_of_logs_even.
  rewrite <- cl_log_even.
  replace (t_size + 1) with (S t_size);[|omega].
  rewrite <- fl_log_cl_log_relationship.
  omega.
Qed.
