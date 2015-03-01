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
  (* the 'cin' (and not true/false) and the '1' don't match up! *)

  (* also, I can't seem to use "unfold_sub plus_cin_time (plus_cin_time 0 0)" *)
  (* like I used to be able to do *)
  admit.
Qed.

Admit Obligations.
