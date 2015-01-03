Require Import Braun.smonad.smonad.
Require Import Braun.smonad.memory.
Require Import Braun.smonad.lists.
Require Import List.
Require Import Omega.

(* XXX I have not tried to write these in the monad, but it seems
scary to do it that way first and maybe not possible due to the
strange recursion scheme *)

Definition MRL_Pre (A:Set) (a_before:Addr) (a_after:Addr)
  : CS_Pre (Memory (SLL A)) :=
  (fun mem =>
    Memory_Valid _ mem /\
    (exists l_before,
      SLL_is_List A mem a_before l_before) /\
    (exists l_after,
      SLL_is_List A mem a_after l_after)).
  
Definition MRL_Post (A:Set) (a_before:Addr) (a_after:Addr)
  : CS_Post (Memory (SLL A)) Addr :=
  (fun mem a_done mrln mem' =>
    Memory_Valid _ mem' /\
    forall l_before l_after,
      SLL_is_List A mem a_before l_before ->
      SLL_is_List A mem a_after l_after ->
      mrln = length l_after /\
      SLL_is_List A mem' a_done ((rev l_after) ++ l_before)).

Definition memory_reverse_loop_unfold_P (A:Set)
  (mem_a_after:((Memory (SLL A))*Addr)) :=
  forall (mem'_a_before:((Memory (SLL A))*Addr)),
    let (mem, a_after) := mem_a_after in
      let (mem', a_before) := mem'_a_before in
        Memory_le (SLL A) mem mem' ->
        forall (PRE:(MRL_Pre A a_before a_after mem)),
          CS_Result (Memory (SLL A)) Addr mem (MRL_Post A a_before a_after).

Program Definition memory_reverse_loop_unfold (A:Set)
  (mem__a_after:((Memory (SLL A))*Addr))  :
  (memory_reverse_loop_unfold_P A mem__a_after).
Proof.
  intros A.
  eapply well_founded_induction.
  apply (SLL_lt_wf A).
  intros [mem0 a_after] IH.
  unfold memory_reverse_loop_unfold_P, MRL_Pre, MRL_Post, CS_Result in *.

  intros [mem a_before] MLE [MV [LB LA]].
  (* xxx use memref *)
  remember (mem_map _ mem0 a_after) as v_after.
  destruct v_after as [v_after|].
  destruct v_after as [v_after a'_after].

  destruct (@malloc _ (NODE A v_after a_before) mem)
    as [[a'_before mem'] Post_malloc].
  eapply Memory_le_Valid. apply MV. apply MLE.

  assert (Memory_le (SLL A) mem0 mem') as MLE'.
   destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
   eauto.

  assert (exists l'_before : list A,
    SLL_is_List A mem' a'_before l'_before) as LB'.
  destruct LB as [l_before LB].
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  exists (cons v_after l_before).
  eapply SiL_cons.
  eapply Memory_le_SiL.
  apply LB. eauto.
  unfold Memory_Extends in ME. intuition.

  assert (exists l'_after : list A,
    SLL_is_List A mem' a'_after l'_after) as LA'.
  destruct LA as [l_after LA].
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  destruct l_after as [|v'_after l_after].
  inversion LA.
   subst mem1 a_after.
   replace (mem_map (SLL A) mem0 NULLptr) with (@None (SLL A)) in *.
   congruence.
   destruct MV as [EQnp [LTnp MV]].
   auto.
  exists l_after.
  eapply Memory_le_SiL.
  inversion LA.
  subst mem1 a v l'.
  rename H3 into LA'.
  rename H4 into MS.
  replace a' with a'_after in *.
  apply LA'.
  congruence.
  eauto.

  assert (SLL_lt A (mem',a'_after) (mem0,a_after)) as Slt.
   eapply SLL_is_List_impl_SLL_lt.
   auto.
   eauto.
   auto. symmetry in Heqv_after. apply Heqv_after.
    
  destruct (IH (mem',a'_after) Slt (mem',a'_before)); clear IH.
  auto.

  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  unfold Memory_Extends in ME. intuition.

  destruct x as [IHa IHmem].
  exists (IHa, IHmem).
  destruct y as [IHn [MV' Post_IH]].
  exists (S IHn).
  split. auto.
  intros l_before l_after LB2 LA2.
  destruct LB' as [l'_before LB'].
  destruct LA' as [l'_after LA'].
  edestruct (Post_IH l'_before l'_after LB') as [EQIHn Post_IH']; clear Post_IH.
  auto.
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  replace l_after with (cons v_after l'_after) in *.
  subst IHn.
  split. simpl. auto.
  replace l'_before with (cons v_after l_before) in *.
  simpl.
  replace ((rev l'_after ++ v_after :: nil) ++ l_before)
    with (rev l'_after ++ v_after :: l_before).
  apply Post_IH'.
  rewrite <- app_assoc.
  simpl. auto.

  remember ME as ME2.
  unfold Memory_Extends in ME.
  destruct ME as [MV2 [MV'2 [MNxt [Same [Diff [MS MN]]]]]].
  inversion LB'.
   subst mem1 a'_before l'_before.
   rename H0 into EQnp'.
   destruct MV2 as [EQnp [LTnp MV2]].
   omega.
  subst mem1 a l'_before.
  rename H into LB'2.
  rename H0 into MS2.
  replace v with v_after in *; try congruence.
  replace l' with l_before in *; auto.
  replace a' with a_before in *; try congruence.
  symmetry.
  eapply SLL_is_List_fun.
  apply MV'2.
  apply LB'2.
  eapply Memory_le_SiL.
  apply LB2.
  auto.

  clear Post_IH' EQmn LB LA.
  inversion LA2.
   subst mem1 a_after l_after.
   replace (mem_map (SLL A) mem0 NULLptr) with (@None (SLL A)) in *.
   congruence.
   destruct MV as [EQnp MV]. auto.
  subst mem1 a l_after.
  rename H0 into MS.
  rewrite <- Heqv_after in MS.
  replace v with v_after in *; try congruence.
  replace l' with l'_after in *; auto.
  replace a' with a'_after in *; try congruence.
  rename H into LA'2.

  eapply SLL_is_List_fun.
  eapply Memory_le_Valid.
  apply MV.
  apply MLE'.
  apply LA'.
  eapply Memory_le_SiL.
  apply LA'2.
  auto.

  exists (a_before, mem0).
  exists 0.
  split. auto.
  clear LB LA.
  intros l_before l_after LB LA.
  replace l_after with (@nil A) in *.
  simpl in *. split. auto. auto.
  inversion LA. auto.
  congruence.
Defined.

Program Definition memory_reverse_loop (A:Set)
  (a_before:Addr) (a_after:Addr) :
  CS (Memory (SLL A))
  (MRL_Pre A a_before a_after)
  Addr
  (MRL_Post A a_before a_after).
Proof.
  intros. intros mem PRE.
  eapply (memory_reverse_loop_unfold (mem,a_after) (mem,a_before)).
  auto. auto.
Defined.

Program Definition memory_reverse (A:Set) (a:Addr) :
  CS (Memory (SLL A))
  (fun mem =>
    Memory_Valid _ mem /\
    (exists l, SLL_is_List A mem a l))
  Addr
  (fun mem a_done mrln mem' =>
    Memory_Valid _ mem' /\
    forall l,
      SLL_is_List A mem a l ->
      mrln = length l /\
      SLL_is_List A mem' a_done (rev l)).
Proof.
  intros. intros mem [MV LA].
  rename a into a_after.
  remember NULLptr as a_before.

  assert (SLL_is_List A mem a_before (@nil A)) as LB.
  subst a_before. auto.

  edestruct (@memory_reverse_loop A a_before a_after mem).
  unfold MRL_Pre.
  split. auto.
  split. exists nil. auto.
  destruct LA as [l_after LA].
  exists l_after. auto.

  destruct x as [a_done mem''].
  exists (a_done, mem'').
  destruct y as [an POST].
  unfold MRL_Post in *.
  exists an.
  destruct POST as [MV'' POST].
  destruct LA as [l_after LA].
  
  edestruct (POST nil l_after) as [EQan LR].
  auto.
  auto.
  split. auto.
  intros l_after' LA'.
  replace l_after' with l_after in *.
  clear l_after' LA'.
  split. auto.
  rewrite app_nil_r in LR. auto.
  eapply SLL_is_List_fun.
  apply MV.
  apply LA.
  apply LA'.
Defined.
