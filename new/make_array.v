Require Import braun log insert.

Section naive1.
  Variable A : Set.

  Inductive MkArrNaive1R : list A -> bin_tree A -> nat -> Prop :=
  | naive1R_zero : MkArrNaive1R nil (bt_mt A) 0
  | naive1R_suc  :
      forall x xs bt bt' time insert_time,
        InsertR A x bt bt' insert_time ->
        MkArrNaive1R        xs bt                  time ->
        MkArrNaive1R (x :: xs) bt' (time + insert_time).
  Hint Constructors MkArrNaive1R.

  Theorem make_array_naive1 :
    forall xs,
      { bt | exists n, MkArrNaive1R xs bt n }.

    induction xs as [| x xs]; [eauto |].
    destruct IHxs as [bt IR].
    remember (insert A x bt).
    clear Heqs.
    destruct s as [bt' insIR'].
    exists bt'.
    destruct IR as [indTime indR].
    destruct insIR' as [insTime insIR].
    exists (indTime + insTime).
    apply (naive1R_suc _ _ bt); eauto.
  Defined.
  
  Theorem MkArrNaive1R_Braun :
    forall xs bt n,
      MkArrNaive1R xs bt n ->
      Braun bt (length xs).

    intro xs.
    induction xs as [| x xs]; intros bt n MkArrR.

    simpl.
    inversion_clear MkArrR.
    constructor.

    simpl.
    inversion_clear MkArrR.
    apply (InsertR_Braun A x (length xs) insert_time bt0).
    apply (IHxs bt0 time H0).
    assumption.
  Qed.

End naive1.
