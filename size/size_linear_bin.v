Require Import Braun.monad.monad Braun.common.big_oh.
Require Import Braun.common.braun Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Section size_linear_bin.
  Variable A : Set.
  
  Definition size_linear_bin_rt n : nat := 17 * n + 3.

  Definition size_linear_bin_result (bt : @bin_tree A) (res:nat) c :=
    forall m,
      Braun bt m ->
      c = size_linear_bin_rt res
      /\ m = res.

  (* the blank line above is important for the paper to build *)
  Definition same :
    forall {P Q R S:Prop},
      (sumbool P Q) -> (sumbool R S) -> (P*R+Q*S) + (P*S+Q*R).
  Proof.
    intuition.
  Qed.

  Load "size_linear_bin_gen.v".

  Next Obligation.
  Proof.
    split; [auto |].
    invclr H.
    auto.
  Qed.

  Next Obligation.
  Proof.
    clear  am H4 am0 H3.
    rename H1 into SLBRr.
    rename H2 into SLBRl.
    rename H into EVENODD.

    unfold size_linear_bin_result in *.
    intros m B.
    invclr B.
    rename H2 into SIZE_INV.
    rename H4 into BL.
    rename H5 into BR.

    remember (SLBRr t_size) as INDr; clear HeqINDr SLBRr.
    apply INDr in BR.
    destruct BR; subst rs an.
    remember (SLBRl s_size) as INDl; clear HeqINDl SLBRl.
    apply INDl in BL.
    destruct BL; subst ls an0.
    clear INDl INDr.

    assert (s_size=t_size).

    apply braun_invariant_odd_size; auto.
    replace (s_size+t_size+1) with (S (s_size+t_size)) by omega.
    constructor.
    destruct EVENODD as [[EVEN_LS EVEN_RS]|[ODD_LS ODD_RS]].
    apply even_even_plus; auto.
    apply odd_even_plus; auto.

    unfold double_plus1; unfold double; unfold size_linear_bin_rt.
    omega.
  Qed.

  Next Obligation.
  Proof.
    clear am H4 am0 H3.
    rename H1 into SLBRr.
    rename H2 into SLBRl.
    rename H into EVENODD.

    unfold size_linear_bin_result in *.
    intros m B.
    invclr B.
    rename H2 into SIZE_INV.
    rename H4 into BL.
    rename H5 into BR.
    remember (SLBRr t_size) as INDr; clear HeqINDr SLBRr.
    apply INDr in BR.
    destruct BR; subst rs an.
    remember (SLBRl s_size) as INDl; clear HeqINDl SLBRl.
    apply INDl in BL.
    destruct BL; subst ls an0.
    clear INDl INDr.

    assert (s_size=t_size+1).
    apply braun_invariant_even_size; auto.
    replace (s_size+t_size+1) with (S (s_size+t_size)) by omega.
    constructor.
    destruct EVENODD as [[EVEN_LS ODD_RS]|[ODD_LS EVEN_RS]].
    apply odd_plus_r; auto.
    apply odd_plus_l; auto.

    unfold double_plus1; unfold double; unfold size_linear_bin_rt.
    omega.
  Qed.

  Theorem size_linear_rt_is_linear : big_oh size_linear_bin_rt (fun n => n).
  Proof.
    unfold size_linear_bin_rt; auto.
  Qed.

End size_linear_bin.
