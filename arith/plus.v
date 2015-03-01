Require Import Program Div2 Omega.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf Init.Wf.
Require Import Coq.Arith.Max.
Require Import Braun.common.util Braun.common.le_util.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Include WfExtensionality.

Program Fixpoint plus_cin_time (n:nat) (m:nat) {measure (m + n)} : nat :=
  match n with
    | 0 => 
      match m with
        | 0 => 7
        | S m' => plus_cin_time 0 (div2 m) + 20
      end
    | S n' => 
      match m with
        | 0 => plus_cin_time (div2 n) 0 + 20
        | S m' => plus_cin_time (div2 n) (div2 m) + 34
      end
  end.

Next Obligation.
Proof.
  repeat (rewrite plus_0_r); auto.
Qed.
Next Obligation.
Proof.
  rewrite plus_0_l; auto.
Qed.  
Next Obligation.
Proof.
  apply plus_lt_compat; auto.
Qed.

Definition plus_cin_result (n:nat) (m:nat) (cin:bool) (res:nat) (c:nat) :=
  n+m+(if cin then 1 else 0)=res /\ c = plus_cin_time n m.
Hint Unfold plus_cin_result.

Load "plus_cin_gen.v".

Next Obligation.
  repeat (rewrite plus_0_r).
  auto.
Qed.

Next Obligation.
  clear H1 am plus_cin.
  rename H0 into PLUSCINRESULT_REC.
  rename Heq_anonymous into EVEN.

  unfold even_oddb in EVEN.
  destruct (even_odd_dec (S m')) in EVEN; [clear EVEN|intuition].
  rename e into EVEN.

  destruct PLUSCINRESULT_REC as [CORRECT TIME].
  split; [clear TIME|clear CORRECT].
  subst mdiv2plusX.
  unfold double_plus_one.
  repeat (rewrite plus_0_r).
  repeat (rewrite plus_0_l).
  rewrite <- even_double; auto.
  omega.

  (*  why doesn't this work?
  unfold_sub plus_cin_time (plus_cin_time 0 (S m')).
*)
  admit.
Qed.

Next Obligation.
  repeat (rewrite plus_0_r).
  auto.
Qed.

Next Obligation.
  clear H1 am plus_cin.
  rename H0 into PLUSCINRESULT_REC.
  rename Heq_anonymous into ODD.

  unfold even_oddb in ODD.
  destruct (even_odd_dec (S m')) in ODD; [intuition|clear ODD].
  rename o into ODD.

  destruct PLUSCINRESULT_REC as [CORRECT TIME].
  split; [clear TIME|clear CORRECT].
  subst mdiv2plusX.
  replace (0+div2(S m')+1) with (S (div2 (S m')));[|omega].
  rewrite odd_div2; auto.
  Type even_double.
  rewrite <- even_double;[|constructor;auto].
  omega.

  admit. (* same question as above! *)
Qed.

Next Obligation.
  clear plus_cin.
  split;simpl.
  omega.

  admit.
Qed.

Next Obligation.
  repeat (rewrite plus_0_l).
  auto.
Qed.  

Admit Obligations.
