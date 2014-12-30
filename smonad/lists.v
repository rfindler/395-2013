Require Import Braun.smonad.smonad.
Require Import Braun.smonad.memory.
Require Import List.
Require Import Omega.

Inductive SLL (A:Set) : Set :=
| NULL : SLL A
| NODE : A -> Addr -> SLL A.
Hint Constructors SLL.

Inductive SLL_is_List (A:Set) : (Memory (SLL A)) -> Addr -> (list A) -> Prop :=
| SiL_nil :
  forall mem a,
    mem_map (SLL A) mem a = Some (NULL A) ->
    SLL_is_List A mem a nil
| SiL_cons :
  forall mem a v l' a',
    SLL_is_List A mem a' l' ->
    mem_map (SLL A) mem a = Some (NODE A v a') ->
    SLL_is_List A mem a (cons v l').
Hint Constructors SLL_is_List.

Lemma SLL_is_List_fun:
  forall A mem a l1,
    SLL_is_List A mem a l1 ->
    forall l2,
      SLL_is_List A mem a l2 ->
      l1 = l2.
Proof.
  intros A mem a l1 S1;
    induction S1; intros l2 S2;
      inversion S2.

  auto.
  congruence.
  congruence.
  
  subst mem0 a0 l2.
  replace v0 with v in *; try congruence.
  replace a'0 with a' in *; try congruence.
  replace l'0 with l' in *; try auto.
Qed.

Lemma memory_extends_SLL:
  forall A mem a' l,
    SLL_is_List A mem a' l ->
    forall a v mem',
      Memory_Extends (SLL A) mem a v mem' ->
      SLL_is_List A mem' a' l.
Proof.
  intros A mem a' n SiL.
  induction SiL as [mem a' MS|mem a' v' l' a'' SiL MS];
    intros a v mem' ME.

  unfold Memory_Extends in ME.
  eapply SiL_nil. intuition.

  eapply (SiL_cons _ _ _ _ _ a'').
  eapply MS. apply ME.
  unfold Memory_Extends in ME.
  intuition.
Qed.

Fixpoint list_of_len (n:nat) : list nat :=
  match n with
    | O =>
      nil
    | S n =>
      cons n (list_of_len n)
  end.

Program Fixpoint memory_list_of_len (n:nat) :
  CS (Memory (SLL nat))
  (fun mem => Memory_Valid _ mem)
  Addr
  (fun mem a an mem' =>
    an = (S n) /\
    Memory_Valid _ mem' /\
    SLL_is_List _ mem' a (list_of_len n))
  :=
  (@inc _ 1 _ _ _
    (match n with
       | O =>
         (@weaken _ _ _ _ _ _ (@malloc (SLL nat) (NULL nat)) _ _)
       | S m =>
         (@weaken _ _ _ _ _ _
           (@bind _ _ _ _
             (@memory_list_of_len m)
             _
             (fun a' a'n mema' =>
               a'n = (S m) /\
               Memory_Valid _ mema' /\
               SLL_is_List _ mema' a' (list_of_len m))
             (fun a' mema' a an mema =>
               an = n /\
               Memory_Valid _ mema /\
               SLL_is_List _ mema a (list_of_len n))
             (fun a' pa' =>
               (@weaken _ _ _ _ _ _ (@malloc (SLL _) (NODE _ m a')) _ _)))
           _ _)
     end)).

Next Obligation.
  rename H2 into ME.
  unfold Memory_Extends in ME.
  repeat split; auto.
  intuition.
  eapply SiL_nil.
  intuition.
Defined.

Next Obligation.
  rename H4 into ME.
  rename H2 into SiLst.
  repeat split; auto.
  unfold Memory_Extends in ME. intuition.
  eapply (SiL_cons _ st' (mem_next (SLL _) st) m _ a');
    try (intuition; fail).
  eapply memory_extends_SLL.
  apply SiLst. apply ME.
  unfold Memory_Extends in ME. intuition.
Defined.

Next Obligation.
  rename H1 into EQm.
  rewrite EQm.
  repeat split; auto.
  omega.
Defined.

Lemma Memory_le_SiL:
  forall (A:Set) mem mem' a_before l_before,
    SLL_is_List A mem a_before l_before ->
    Memory_le (SLL A) mem mem' ->
    SLL_is_List A mem' a_before l_before.
Proof.
  intros A mem mem' a_before l_before SiL MLE.
  generalize mem' MLE. clear mem' MLE.
  induction SiL; intros mem' MLE.

  rename H into MS.
  eapply SiL_nil.
  apply (Memory_le_Same (SLL A) mem mem' MLE a _ MS).

  rename H into MS.
  eapply SiL_cons.
  eapply IHSiL. apply MLE.
  apply (Memory_le_Same (SLL A) mem mem' MLE a _ MS).
Qed.

Inductive SLL_lt_core (A:Set) (mem:Memory (SLL A)) : Addr -> Addr -> Prop :=
| Sltc_NULL :
  forall to from v,
    mem_map (SLL A) mem to = Some (NULL A) ->
    mem_map (SLL A) mem from = Some (NODE A v to) ->
    SLL_lt_core A mem to from
| Sltc_NODE :
  forall to next from v v',
    (* This ensures that there is no cycle, because Coq won't let us
       construct one that doesn't end in a Sltc_NULL *)
    SLL_lt_core A mem next to ->
    mem_map (SLL A) mem to = Some (NODE A v' next) ->
    mem_map (SLL A) mem from = Some (NODE A v to) ->
    SLL_lt_core A mem to from.
Hint Constructors SLL_lt_core.

Definition SLL_lt (A:Set) (mem_to:((Memory (SLL A))*Addr))
  (mem_from:((Memory (SLL A))*Addr)) :=
  let (mem', to) := mem_to in
  let (mem, from) := mem_from in
    Memory_le (SLL A) mem mem' /\
    SLL_lt_core A mem to from.
Hint Unfold SLL_lt.

Theorem SLL_lt_wf:
  forall A,
    well_founded (SLL_lt A).
Proof.
  intros A [mem from1].
  eapply Acc_intro.
  intros [mem' to1] Slt1.

  unfold SLL_lt in *; simpl in *.

  destruct Slt1 as [MLE1 Sltc1].
  generalize mem' MLE1.
  clear mem' MLE1.
  induction Sltc1; intros mem' MLE1.

  rename to into to1.
  rename from into from1.
  rename H into MS_to1.
  rename H0 into MS_from1.
  eapply Acc_intro.
  intros [mem2 to2] Slt2.
  destruct Slt2 as [MLE2 Sltc2].
  inversion Sltc2; clear Sltc2.
  subst to from.
  rename H into MS_to2.
  rename H0 into MS_to1'.
  eapply (Memory_le_Same _ mem mem') in MS_to1; auto.
  congruence.
  subst to from.
  rename H into Sltc3.
  rename H0 into MS_to2.
  rename H1 into MS_to1'. 
  eapply (Memory_le_Same _ mem mem') in MS_to1; auto.
  congruence.

  rename to into to1.
  rename from into from1.
  rename H into MS_to1.
  rename H0 into MS_from1.
  eapply Acc_intro.
  intros [mem2 to2] Slt2.
  destruct Slt2 as [MLE2 Sltc2].
  inversion Sltc2; clear Sltc2.
  subst to from.
  rename H into MS_to2.
  rename H0 into MS_to1'.
  eapply (Memory_le_Same _ mem mem') in MS_to1; auto.
  replace v0 with v' in *; try congruence; clear v0.
  replace to2 with next in *; try congruence; clear to2.
  eapply IHSltc1. eauto.

  subst to from.
  rename H into Sltc3.
  rename H0 into MS_to2.
  rename H1 into MS_to1'.
  eapply (Memory_le_Same _ mem mem') in MS_to1; auto.
  replace v0 with v' in *; try congruence; clear v0.
  replace to2 with next in *; try congruence; clear to2.
  clear MS_to1'.
  eapply IHSltc1. eauto.
Qed.  

Lemma SLL_is_List_impl_SLL_lt:
  forall (A:Set) mem mem' a_after v_after a'_after,
    Memory_le (SLL A) mem mem' ->
    (exists l_after : list A, SLL_is_List A mem a_after l_after) ->
    mem_map (SLL A) mem a_after = Some (NODE A v_after a'_after) ->
    SLL_lt A (mem',a'_after) (mem,a_after).
Proof.
  intros A mem mem' a_after v_after a'_after MLE [l_after SiL] MS.
  generalize mem' v_after a'_after MLE MS.
  clear mem' v_after a'_after MLE MS.
  induction SiL; intros mem' v_after a'_after MLE MS.
  congruence.
  rename H into MS'.
  replace v with v_after in *; try congruence; clear v.
  replace a' with a'_after in *; try congruence; clear a'.
  clear MS'.
  unfold SLL_lt.
  inversion SiL; eauto.
  subst mem0 a0 l'.
  rename H0 into MS'.
  split; auto.
  eapply Sltc_NODE.
  eapply IHSiL.
  apply MLE.
  apply MS'.
  apply MS'.
  apply MS.
Qed.

