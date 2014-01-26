Require Import Braun.tmonad.monad.
Require Import Braun.common.util.
Require Import Arith Arith.Even Arith.Div2.
Require Import Coq.Program.Wf.

Definition sub1_result (n:nat) (res:nat) (c:nat) := n-1 = res.
Hint Unfold sub1_result.

(* this file was generated automatically *)
Program Fixpoint sub1 (n:nat) {measure n}
: {! res !:! nat !<! c !>!
     sub1_result n res c !} :=
  match n with
    | 0 => 
      += 3; 
      <== 0
    | S _ => 
      if (even_odd_dec n)
      then (sd2 <- sub1 (div2 n);
            += 12; 
            <== (sd2 + sd2 + 1))
      else (+= 8; 
            <== (n - 1))
  end.

Next Obligation.
  clear H2 xm.
  rename H into EW.
  unfold sub1_result in *.
  subst sd2.
  rewrite (even_double (S wildcard')) at 1; auto.
  unfold double.
  remember (div2 (S wildcard')) as x.
  destruct x; try omega.

  destruct wildcard'.
  inversion EW.
  inversion H0.
  simpl in Heqx.
  inversion Heqx.
Qed.
