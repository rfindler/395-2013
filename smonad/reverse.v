Require Import Braun.smonad.smonad.
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

Inductive SLL : Set :=
| NULL : SLL
| NODE :
  nat -> Addr -> SLL.
Hint Constructors SLL.

Inductive SLL_is_List : (Memory SLL) -> Addr -> nat -> Prop :=
| SiL_nil :
  forall mem a,
    mem_map SLL mem a = Some NULL ->
    SLL_is_List mem a 0
| SiL_cons :
  forall mem a n a',
    SLL_is_List mem a' n ->
    mem_map SLL mem a = Some (NODE n a') ->
    SLL_is_List mem a (S n).
Hint Constructors SLL_is_List.

Lemma memory_extends_SLL:
  forall mem a' n,
    SLL_is_List mem a' n ->
    forall a v mem',
      Memory_Extends SLL mem a v mem' ->
      SLL_is_List mem' a' n.
Proof.
  intros mem a' n SiL.
  induction SiL as [mem a' MS|mem a' n a'' SiL MS];
    intros a v mem' ME.

  unfold Memory_Extends in ME.
  eapply SiL_nil. intuition.

  eapply (SiL_cons _ _ _ a'').
  eapply MS. apply ME.
  unfold Memory_Extends in ME.
  intuition.
Qed.

Program Fixpoint memory_list_of_len (n:nat) :
  CS (Memory SLL) (fun mem => Memory_Valid _ mem) Addr
  (fun mem a an mem' =>
    an = (S n) /\
    Memory_Valid _ mem' /\
    SLL_is_List mem' a n)
  :=
  (@inc _ 1 _ _ _
    (match n with
       | O =>
         (@weaken _ _ _ _ _ _ (@malloc SLL NULL) _ _)
       | S m =>
         (@weaken _ _ _ _ _ _
           (@bind _ _ _ _
             (@memory_list_of_len m)
             _
             (fun a' a'n mema' =>
               a'n = (S m) /\
               Memory_Valid _ mema' /\
               SLL_is_List mema' a' m)
             (fun a' mema' a an mema =>
               an = n /\
               Memory_Valid _ mema /\
               SLL_is_List mema a n)
             (fun a' pa' =>
               (@weaken _ _ _ _ _ _ (@malloc SLL (NODE m a')) _ _)))
           _ _)
     end)).

Solve Obligations using auto.

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
  eapply (SiL_cons st' (mem_next SLL st) m a');
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
