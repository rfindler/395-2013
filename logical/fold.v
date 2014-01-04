Require Import Braun.logical.util List Omega.

(* XXX I tried to use this for Make_Array_Linear, but it failed. *)

Section fold.
  Variable A : Set.
  Variable B : Set.
  Variable R : A -> B -> B -> nat -> Prop.
  Hypothesis R_dec :
    forall a b,
      { b' | exists rt, R a b b' rt } +
      { forall b' rt, ~ R a b b' rt }.
  Hypothesis R_fun:
    forall a b b' rt,
      R a b b' rt ->
      forall _b' _rt,
        R a b _b' _rt ->
        b' = _b' /\ rt = _rt.

  Inductive FoldR : B -> list A -> B -> nat -> Prop :=
  | FoldR_mt :
      forall b,
        FoldR b nil b 0
  | FoldR_cons :
      forall a aa b b' b'' rt ft,
        R a b b' rt ->
        FoldR b' aa b'' ft ->
        FoldR b (a::aa) b'' (rt + ft + 1).
  Hint Constructors FoldR.

  Theorem FoldR_dec :
    forall aa b,
      { b' | exists ft, FoldR b aa b' ft } +
      { forall b' ft, ~ FoldR b aa b' ft }.
  Proof.
    induction aa as [|a aa]; intros b.

    left. eauto.

    destruct (R_dec a b) as [[b' RP]|RFAIL].
    destruct (IHaa b') as [[b'' FP]|IFAIL].
    left. exists b''.
    destruct RP as [rt RP].
    destruct FP as [ft FP].
    eauto.

    right. intros _b' _ft FR.
    destruct RP as [rt RP].
    invclr FR.
    replace b'0 with b' in *.
    apply IFAIL in H5. auto.
    destruct (R_fun _ _ _ _ RP _ _ H2).
    auto.

    right. intros b' ft FR.
    invclr FR. apply RFAIL in H2. auto.
  Defined.

  Hypothesis r :
    forall a b,
      { b' | exists rt, R a b b' rt }.

  (* XXX It would be nice to build this on FoldR_dec *)
  Theorem fold :
    forall aa b,
      { b' | exists ft, FoldR b aa b' ft }.
  Proof.
    induction aa as [|a aa]; intros b.

    eauto.

    destruct (r a b) as [b' RP].
    destruct (IHaa b') as [b'' FP].
    exists b''.
    destruct RP as [rt RP].
    destruct FP as [ft FP].
    eauto.
  Defined.
End fold.
