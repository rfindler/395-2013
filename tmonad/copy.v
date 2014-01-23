Require Import Braun.tmonad.monad Braun.logical.index.
Require Import Braun.common.braun Braun.common.log Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Definition copy_rt n := cl_log (n + 1) + fl_log n.
Lemma copy_rt_Sn : forall n, copy_rt (div2 n) + 2 = copy_rt (n + 1).
Proof.
  intros n.
  unfold copy_rt.
  replace (n+1+1) with (S (n+1));[|omega].
  replace (n+1) with (S n);[|omega].
  rewrite <- fl_log_div2.
  rewrite cl_log_div2'.
  replace (div2 (S (S n))) with (div2 n+1); [|simpl;omega].
  omega.
Qed.

Definition copy2_result (A:Set) (x:A) n (pr:bin_tree * bin_tree) c :=
  let (s,t) := pr in
  Braun s (n+1) /\
  Braun t n /\
  (forall i y, IndexR s i y -> y = x) /\
  (forall i y, IndexR t i y -> y = x) /\
  c = copy_rt n.

Load "copy2_gen.v".

Next Obligation.
Proof.
  (* zero case *)
  replace 1 with (0+0+1);[|omega].
  repeat split; try (constructor; try omega; auto).

  intros i y IR; invclr IR.
  auto.
  invclr H4.
  invclr H4.

  intros i y IR; invclr IR.

  admit.
Qed.

Next Obligation.
Proof. 
  (* even case *)

  rename H into EVENn'.

  apply even_double in EVENn'; unfold double in EVENn'.

  (* proof of braun preservation *)
  replace (S (n'+1)) with ((div2 n' + 1)+(div2 n')+1);[|omega].
  replace (S n') with (div2 n' + div2 n' + 1);[|omega].
  repeat constructor; try omega; try assumption.

  (* proof of correct elems *)
  intros i y IR. clear EVENn'. invclr IR; eauto.
  intros i y IR. clear EVENn'. invclr IR; eauto.

  (* proof of running time *)
  rewrite <- EVENn'.
  admit.
  (* apply copy_rt_Sn. *)
Qed.

Next Obligation.
Proof.
  (* odd case *)

  rename H into ODDn'.
  apply odd_double in ODDn'; unfold double in ODDn'.

  (* proof of braun preservation *)
  replace (S (n'+1)) with ((div2 n'+1) + (div2 n'+1) + 1);[|omega].
  replace (S n') with ((div2 n'+1) + (div2 n') + 1);[|omega].
  repeat constructor; try omega; try assumption.

  (* proof of correct elems *)
  intros i y IR. clear ODDn'. invclr IR; eauto.
  intros i y IR. clear ODDn'. invclr IR; eauto.
  
  (* proof of running time *)
  replace (div2 n' + 1 + div2 n' + 1) with (n'+1);[|omega].
  (* apply copy_rt_Sn. *) admit.
Qed.

Definition copy_result (A:Set) (x:A) (n:nat) (b:@bin_tree A) c :=
  Braun b n /\ 
  (forall i y, IndexR b i y -> y = x) /\
  c = copy_rt n.

Load "copy_gen.v".

Next Obligation.
  unfold copy_result.
  unfold copy2_result in *.
  intuition.

  admit. (* running time proof .... *)
Qed.
