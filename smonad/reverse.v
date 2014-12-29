Require Import Braun.smonad.smonad.
Require Import List.
Require Import Omega.

Definition Addr := nat.
Hint Unfold Addr.

Definition addr_inc (a:Addr) : Addr := S a.

Theorem addr_eq_dec:
  forall (x y:Addr),
    {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition Map (C:Set) := (Addr -> option C).
Hint Unfold Map.

Definition map_ext (C:Set) (m:Map C) (a:Addr) (v:C) : Map C :=
  fun a' =>
    match addr_eq_dec a a' with
      | left _ => Some v
      | right _ => m a'
    end.
Hint Unfold map_ext.

Lemma map_ext_eq:
  forall C m a v,
    map_ext C m a v a = Some v.
Proof.
  intros.
  unfold map_ext.
  destruct (addr_eq_dec a a); eauto.
  congruence.
Qed.
Hint Resolve map_ext_eq.

Lemma map_ext_neq:
  forall C m a v a',
    a <> a' ->
    map_ext C m a v a' = m a'.
Proof.
  intros. unfold map_ext.
  destruct (addr_eq_dec a a'); eauto.
  congruence.
Qed.
Hint Resolve map_ext_neq.

Lemma map_ext_some:
  forall C m a v a' v',
    m a = None ->
    m a' = Some v' ->
    (map_ext C m a v) a' = Some v'.
Proof.
  intros C m a v a' v' MN MS.
  rewrite <- MS.
  eapply map_ext_neq.
  intros EQ. congruence.
Qed.
Hint Resolve map_ext_some.

Lemma map_ext_none:
  forall C m a v a',
    m a = None ->
    a <> a' ->
    (map_ext C m a' v) a = None.
Proof.
  intros C m a v a' MN NEQ.
  rewrite <- MN.
  eapply map_ext_neq.
  intros EQ. congruence.
Qed.
Hint Resolve map_ext_none.

Definition Memory (C:Set) : Set := (Addr * (Map C))%type.
Hint Unfold Memory.

Definition mem_next (C:Set) (mem:Memory C) := fst mem.
Hint Unfold mem_next.
Definition mem_map (C:Set) (mem:Memory C) := snd mem.
Hint Unfold mem_map.

Definition Memory_Valid (C:Set) (mem:Memory C) :=
  forall a,
    (mem_next C mem) <= a ->
    ((mem_map C mem) a) = None.
Hint Unfold Memory_Valid.

Definition Memory_Extends (C:Set) (mem:Memory C) (last:Addr) (init:C) (mem':Memory C) :=
  Memory_Valid C mem /\
  Memory_Valid C mem' /\
  mem_next C mem' = addr_inc (mem_next C mem) /\
  (* mem' contains everything from mem *)
  (forall (a:Addr) (c:C), mem_map C mem a = Some c -> mem_map C mem' a = Some c) /\
  (* if mem' contains something more, then it is last *)
  (exists (a:Addr) (c:C), mem_map C mem' a = Some c /\ mem_map C mem a = None ->
    a = last /\ c = init) /\
  (* mem' contains last *)
  mem_map C mem' last = Some init /\
  (* mem doesn't contain last *)
  mem_map C mem last = None.

Definition Memory_Modifies (C:Set) (mem:Memory C) (a:Addr) (av':C) (mem':Memory C) :=
  mem_next C mem' = mem_next C mem  /\
  mem_map C mem' a = Some av' /\
  forall (a':Addr),
    mem_map C mem' a' = mem_map C mem a'
    \/ a = a'.

(* XXX It is _really_ painful to write these in the monad. *)
Program Definition malloc (C:Set) (init:C) :
  (CS (Memory C) (fun mem => Memory_Valid C mem) Addr
    (fun mem next allocn mem' =>
      next = (mem_next C mem) /\
      allocn = 0 /\
      Memory_Extends C mem next init mem')).
Proof.
  intros C init mem MV.
  destruct mem as [next map].
  exists (next, (addr_inc next, map_ext C map next init)).
  exists 0.
  unfold Memory_Extends.
  unfold Memory_Valid in *.
  simpl in *.
  repeat split; eauto.

  intros a LE.
  unfold addr_inc in *.
  eapply map_ext_none.
  eapply MV. omega. omega.
Defined.

Program Definition mref (C:Set) (a:Addr) :
  (CS (Memory C) (fun mem => True) (option C)
    (fun mem av refn mem' =>
      av = mem_map C mem a /\
      refn = 0 /\
      mem' = mem)).
Proof.
  intros C a mem P.
  destruct mem as [next map].
  exists (map a, (next, map)).
  simpl. eauto.
Defined.

Program Definition mset (C:Set) (a:Addr) (av':C) :
  (CS (Memory C) (fun mem => True) unit
    (fun mem _ setn mem' =>
      setn = 0 /\
      Memory_Modifies C mem a av' mem')).
Proof.
  intros C a av' mem P.
  destruct mem as [next map].
  exists (tt, (next, map_ext C map a av')).
  exists 0. split. auto.
  unfold Memory_Modifies.
  simpl.
  repeat split; eauto.
  intros a'.
  destruct (addr_eq_dec a a'); eauto.
Defined.

(* example *)

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

(* XXX I have not tried to write these in the monad, but it seems
scary to do it that way first *)

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

(* XXX change this to (Mem,Addr) x (Mem,Addr) so that the TO mem can be changing during the induction and integrate back up the memory_extends, perhaps via Mem_lt *)
Inductive SLL_lt (A:Set) (mem:(Memory (SLL A))) : Addr -> Addr -> Prop :=
| Slt_NULL :
  forall to from v,
    mem_map (SLL A) mem to = Some (NULL A) ->
    mem_map (SLL A) mem from = Some (NODE A v to) ->
    SLL_lt A mem to from
| Slt_NODE :
  forall to next from v v',
    SLL_lt A mem next to ->
    mem_map (SLL A) mem to = Some (NODE A v' next) ->
    mem_map (SLL A) mem from = Some (NODE A v to) ->
    SLL_lt A mem to from.
Hint Constructors SLL_lt.

Theorem SLL_lt_wf:
  forall A mem,
    well_founded (SLL_lt A mem).
Proof.
  intros A mem from1.
  eapply Acc_intro.
  intros to1 Slt1.

  induction Slt1.

  rename H into MS_to.
  rename H0 into MS_from.
  eapply Acc_intro.
  intros to2 Slt2.
  inversion Slt2; clear Slt2.
  congruence.
  subst from0 to0.
  congruence.

  rename H into MS_to.
  rename H0 into MS_from.
  eapply Acc_intro.
  intros to2 Slt2.
  inversion Slt2; clear Slt2.
  subst to0 from0.
  congruence.

  subst to0 from0.
  congruence.
Qed.

Lemma SLL_is_List_impl_SLL_lt:
  forall (A:Set) mem a_after v_after a'_after,
    (exists l_after : list A, SLL_is_List A mem a_after l_after) ->
    mem_map (SLL A) mem a_after = Some (NODE A v_after a'_after) ->
    SLL_lt A mem a'_after a_after.
Proof.
  intros.
  rename H0 into MS.
  destruct H as [l_after SiL].
  generalize a'_after v_after MS. clear MS a'_after v_after.
  induction SiL; intros a'_after v_after MS.
  congruence.
  rename H into MS'.
  replace v with v_after in *; try congruence; clear v.
  replace a' with a'_after in *; try congruence; clear a'.
  clear MS'.
  inversion SiL; eauto.
Qed.

Definition memory_reverse_loop_unfold_P (A:Set)
  (mem:(Memory (SLL A))) (a_after:Addr) :=
  forall (a_before:Addr)
    (PRE:(MRL_Pre A a_before a_after mem)),
    CS_Result (Memory (SLL A)) Addr mem (MRL_Post A a_before a_after).

Program Definition memory_reverse_loop_unfold (A:Set)
  (mem:(Memory (SLL A))) (a_after:Addr)  :
  (memory_reverse_loop_unfold_P A mem a_after).
Proof.
  intros A mem.
  eapply well_founded_induction.
  apply (SLL_lt_wf A mem).
  intros a_after IH.
  unfold memory_reverse_loop_unfold_P, MRL_Pre, MRL_Post, CS_Result in *.

  intros a_before [MV [LB LA]].
  remember (mem_map _ mem a_after) as v_after.
  destruct v_after as [v_after|].

  Focus 2.
   cut False. intuition.
   destruct LA as [l_after LA].
   inversion LA; congruence.
  
  destruct v_after as [|v_after a'_after].

  exists (a_before, mem).
  exists 0.
  split. auto.
  clear LB LA.
  intros l_before l_after LB LA.
  replace l_after with (@nil A) in *.
  simpl in *. split. auto. auto.
  inversion LA. auto.
  congruence.

  destruct (@malloc _ (NODE A v_after a_before) mem)
    as [[a'_before mem'] Post_malloc].
  auto.

  assert (exists l'_before : list A,
    SLL_is_List A mem' a'_before l'_before) as LB'. 
  destruct LB as [l_before LB].
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  exists (cons v_after l_before).
  eapply SiL_cons.
  eapply memory_extends_SLL.
  apply LB. apply ME.
  unfold Memory_Extends in ME. intuition.

  assert (exists l'_after : list A,
    SLL_is_List A mem' a'_after l'_after) as LA'.
  destruct LA as [l_after LA].
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  destruct l_after as [|v'_after l_after].
  inversion LA. congruence.
  exists l_after.
  eapply memory_extends_SLL.
  inversion LA.
  subst mem0 a v l'.
  rename H3 into LA'.
  rename H4 into MS.
  replace a' with a'_after in *.
  apply LA'.
  congruence.
  apply ME.

  assert (SLL_lt A mem a'_after a_after) as Slt.
  eapply SLL_is_List_impl_SLL_lt.
  apply LA. symmetry. apply Heqv_after.
  
  (* XXX want to use mem' *)
  destruct (IH a'_after Slt a'_before).

  destruct (IHl_after_len a'_before a'_after mem');
    clear IHl_after_len.
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  unfold Memory_Extends in ME. intuition.

  destruct x as [IHa IHmem].
  exists (IHa, IHmem).
  destruct y as [IHn [MV' Post_IH]].
  exists (S IHn).
  split. auto.
  intros l_before l_after LB2 [LA2 EQLA2].
  destruct LB' as [l'_before LB'].
  destruct LA' as [l'_after [LA' EQLA']].
  edestruct (Post_IH l'_before l'_after LB') as [EQIHn Post_IH'].
  auto.
  subst IHn. split.
  omega.
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  replace l'_before with (cons v_after l_before) in *.
  replace l_after with (cons v_after l'_after) in *.
  simpl.
  replace ((rev l'_after ++ v_after :: nil) ++ l_before)
    with (rev l'_after ++ v_after :: l_before).
  apply Post_IH'.
  rewrite <- app_assoc.
  simpl. auto.

  clear Post_IH' Post_IH EQmn LB LA.
  inversion LA2. congruence.
  subst mem0 a l_after.
  rename H0 into MS.
  rewrite <- Heqv_after in MS.
  replace v with v_after in *; try congruence.
  replace l' with l'_after in *; auto.
  replace a' with a'_after in *; try congruence.
  rename H into LA'2.

  eapply SLL_is_List_fun.
  apply LA'.
  eapply memory_extends_SLL.
  apply LA'2.
  apply ME.

  remember ME as ME2.
  unfold Memory_Extends in ME.
  destruct ME as [MV2 [MV'2 [MNxt [Same [Diff [MS MN]]]]]].
  inversion LB'. congruence.
  subst mem0 a l'_before.
  rename H into LB'2.
  rename H0 into MS2.
  replace v with v_after in *; try congruence.
  replace l' with l_before in *; auto.
  replace a' with a_before in *; try congruence.
  symmetry.
  eapply SLL_is_List_fun.
  apply LB'2.
  eapply memory_extends_SLL.
  apply LB2.
  apply ME2.
  
Defined.

Program Definition memory_reverse_loop (A:Set)
  (a_before:Addr) (a_after:Addr) :
  CS (Memory (SLL A))
  (MRL_Pre A a_before a_after)
  Addr
  (MRL_Post A a_before a_after).
Proof.
  intros A a_before a_after mem PRE.
  assert (SLL_is_Some_List A mem a_after) as SiSL.
  apply SiL_iff_SiSL. intuition.
  generalize PRE. clear PRE.
  generalize a_before. clear a_before.

  induction SiSL.

  SiL_iff_SiSL
  
  intros A l_after_len .
  induction l_after_len as [|l_after_len];
    intros a_before a_after mem [MV [LB LA]];
      (* XXX replace with use of mref *)
      remember (mem_map _ mem a_after) as v_after.

  (* nil *)
  destruct v_after as [v_after|].
  destruct v_after as [|v_after a'_after].
  exists (a_before, mem).
  exists 0.
  split. auto.
  clear LB LA.
  intros l_before l_after LB [LA EQ].
  replace l_after with (@nil A) in *.
  simpl in *. split. auto.
  simpl_list. auto.
  inversion LA. auto.
  congruence.

  cut False. intuition.
  destruct LA as [l_after [LA EQ]].
  inversion LA. subst mem0 a l_after.
  congruence.
  subst mem0 a l_after. simpl in *.
  congruence.

  cut False. intuition.
  destruct LA as [l_after [LA EQ]].
  inversion LA; congruence.

  (* cons *)
  destruct v_after as [v_after|].
  destruct v_after as [|v_after a'_after].

  cut False. intuition.
  destruct LA as [l_after [LA EQ]].
  inversion LA. subst mem0 a l_after.
  simpl in EQ. congruence.
  congruence.

  destruct (@malloc _ (NODE A v_after a_before) mem)
    as [[a'_before mem'] Post_malloc].
  auto.

  assert (exists l'_before : list A,
    SLL_is_List A mem' a'_before l'_before) as LB'. 
  destruct LB as [l_before LB].
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  exists (cons v_after l_before).
  eapply SiL_cons.
  eapply memory_extends_SLL.
  apply LB. apply ME.
  unfold Memory_Extends in ME. intuition.

  assert (exists l'_after : list A,
    SLL_is_List A mem' a'_after l'_after /\
    length l'_after = l_after_len) as LA'.
  destruct LA as [l_after [LA EQ]].
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  destruct l_after as [|v'_after l_after].
  simpl in EQ. congruence.
  exists l_after.
  split; auto.
  eapply memory_extends_SLL.
  inversion LA.
  subst mem0 a v l'.
  rename H3 into LA'.
  rename H4 into MS.
  replace a' with a'_after in *.
  apply LA'.
  congruence.
  apply ME.

  destruct (IHl_after_len a'_before a'_after mem');
    clear IHl_after_len.
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  unfold Memory_Extends in ME. intuition.

  destruct x as [IHa IHmem].
  exists (IHa, IHmem).
  destruct y as [IHn [MV' Post_IH]].
  exists (S IHn).
  split. auto.
  intros l_before l_after LB2 [LA2 EQLA2].
  destruct LB' as [l'_before LB'].
  destruct LA' as [l'_after [LA' EQLA']].
  edestruct (Post_IH l'_before l'_after LB') as [EQIHn Post_IH'].
  auto.
  subst IHn. split.
  omega.
  destruct Post_malloc as [mn [EQa'_before [EQmn ME]]].
  replace l'_before with (cons v_after l_before) in *.
  replace l_after with (cons v_after l'_after) in *.
  simpl.
  replace ((rev l'_after ++ v_after :: nil) ++ l_before)
    with (rev l'_after ++ v_after :: l_before).
  apply Post_IH'.
  rewrite <- app_assoc.
  simpl. auto.

  clear Post_IH' Post_IH EQmn LB LA.
  inversion LA2. congruence.
  subst mem0 a l_after.
  rename H0 into MS.
  rewrite <- Heqv_after in MS.
  replace v with v_after in *; try congruence.
  replace l' with l'_after in *; auto.
  replace a' with a'_after in *; try congruence.
  rename H into LA'2.

  eapply SLL_is_List_fun.
  apply LA'.
  eapply memory_extends_SLL.
  apply LA'2.
  apply ME.

  remember ME as ME2.
  unfold Memory_Extends in ME.
  destruct ME as [MV2 [MV'2 [MNxt [Same [Diff [MS MN]]]]]].
  inversion LB'. congruence.
  subst mem0 a l'_before.
  rename H into LB'2.
  rename H0 into MS2.
  replace v with v_after in *; try congruence.
  replace l' with l_before in *; auto.
  replace a' with a_before in *; try congruence.
  symmetry.
  eapply SLL_is_List_fun.
  apply LB'2.
  eapply memory_extends_SLL.
  apply LB2.
  apply ME2.

  clear IHl_after_len.
  cut False. intuition.
  destruct LA as [l_after [LA EQ]].
  inversion LA; congruence.
Defined.  

(* XXX Call and start it off *)
