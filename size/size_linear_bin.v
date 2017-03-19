Require Import Braun.monad.monad Braun.common.big_oh.
Require Import Braun.common.braun Braun.common.util.
Require Import Arith Arith.Even Arith.Div2 Omega.

Section size_linear_bin.
  Variable A : Set.
  
  Definition size_linear_bin_rt n : nat := 17 * n + 3.

  Definition size_linear_bin_result (bt : @bin_tree A) (n:nat) c :=
    (forall m, Braun bt m ->
               c = size_linear_bin_rt n /\ m = n).

  Load "size_linear_bin_gen.v".

  Next Obligation.
  Proof.
    split; [auto |].
    invclr H.
    auto.
  Qed.

  Next Obligation.
  Proof.
    clear am0 H4 am H5.
    rename H2 into SLBRr.
    rename H3 into SLBRl.

    unfold size_linear_bin_result in *.
    intros m B.
    invclr B.
    rename H4 into SIZE_INV.
    rename H6 into BL.
    rename H7 into BR.
    remember (SLBRr t_size) as INDr; clear HeqINDr SLBRr.
    apply INDr in BR.
    destruct BR; subst rs an.
    remember (SLBRl s_size) as INDl; clear HeqINDl SLBRl.
    apply INDl in BL.
    destruct BL; subst ls an0.
    clear INDl INDr.

    assert (s_size=t_size).
    apply braun_invariant_odd_size; auto.
    replace (s_size+t_size+1) with (s_size+(S t_size)) by omega.
    apply odd_plus_r; auto.
    constructor.
    auto.

    unfold double_plus1; unfold double; unfold size_linear_bin_rt.
    omega.
  Qed.

  Next Obligation.
  Proof.
    clear am0 H4 am H5.
    rename H2 into SLBRr.
    rename H3 into SLBRl.

    unfold size_linear_bin_result in *.
    intros m B.
    invclr B.
    rename H4 into SIZE_INV.
    rename H6 into BL.
    rename H7 into BR.
    remember (SLBRr t_size) as INDr; clear HeqINDr SLBRr.
    apply INDr in BR.
    destruct BR; subst rs an.
    remember (SLBRl s_size) as INDl; clear HeqINDl SLBRl.
    apply INDl in BL.
    destruct BL; subst ls an0.
    clear INDl INDr.

    assert (s_size=t_size+1).
    apply braun_invariant_even_size; auto.
    replace (s_size+t_size+1) with (s_size+(S t_size)) by omega.
    apply even_even_plus; auto.
    constructor.
    auto.

    unfold double_plus1; unfold double; unfold size_linear_bin_rt.
    omega.
  Qed.

  Next Obligation.
  Proof.
    clear am0 H4 am H5.
    rename H2 into SLBRr.
    rename H3 into SLBRl.

    unfold size_linear_bin_result in *.
    intros m B.
    invclr B.
    rename H4 into SIZE_INV.
    rename H6 into BL.
    rename H7 into BR.
    remember (SLBRr t_size) as INDr; clear HeqINDr SLBRr.
    apply INDr in BR.
    destruct BR; subst rs an.
    remember (SLBRl s_size) as INDl; clear HeqINDl SLBRl.
    apply INDl in BL.
    destruct BL; subst ls an0.
    clear INDl INDr.

    assert (s_size=t_size+1).

    apply braun_invariant_even_size; auto.
    replace (s_size+t_size+1) with ((S s_size) + t_size) by omega.
    apply even_even_plus; auto.
    constructor.
    auto.

    unfold double_plus1; unfold double; unfold size_linear_bin_rt.
    omega.
  Qed.

  Next Obligation.
  Proof.
    clear am0 H4 am H5.
    rename H2 into SLBRr.
    rename H3 into SLBRl.

    unfold size_linear_bin_result in *.
    intros m B.
    invclr B.
    rename H4 into SIZE_INV.
    rename H6 into BL.
    rename H7 into BR.
    remember (SLBRr t_size) as INDr; clear HeqINDr SLBRr.
    apply INDr in BR.
    destruct BR; subst rs an.
    remember (SLBRl s_size) as INDl; clear HeqINDl SLBRl.
    apply INDl in BL.
    destruct BL; subst ls an0.
    clear INDl INDr.

    assert (s_size=t_size).
    apply braun_invariant_odd_size; auto.
    replace (s_size+t_size+1) with ((S s_size) + t_size) by omega.
    apply odd_plus_r; auto.
    constructor.
    auto.

    unfold double_plus1; unfold double; unfold size_linear_bin_rt.
    omega.
  Qed.

  Theorem size_linear_rt_is_linear : big_oh size_linear_bin_rt (fun n => n).
  Proof.
    unfold size_linear_bin_rt; auto.
  Qed.

End size_linear_bin.
