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

Inductive Memory_le A : (Memory A) -> (Memory A) -> Prop :=
| Mle_eq:
  forall mem,
    Memory_le A mem mem
| Mle_me:
  forall mem mem' last init,
    Memory_Extends A mem last init mem' ->
    Memory_le A mem mem'
| Mle_trans:
  forall mem0 mem1 mem2,
    Memory_le A mem0 mem1 ->
    Memory_le A mem1 mem2 ->
    Memory_le A mem0 mem2.
Hint Constructors Memory_le.

Lemma Memory_le_Valid:
  forall A mem mem',
    Memory_Valid A mem ->
    Memory_le A mem mem' ->
    Memory_Valid A mem'.
Proof.
  intros A mem mem' MV MLE.
  induction MLE; eauto.
  unfold Memory_Extends in *.
  intuition.
Qed.

Lemma Memory_le_Same:
  forall A mem mem',
    Memory_le A mem mem' ->
    forall a v,
      mem_map A mem a = Some v ->
      mem_map A mem' a = Some v.
Proof.
  intros A mem mem' MLE.
  induction MLE; intros a v MS.

  auto.

  unfold Memory_Extends in *.
  intuition.

  eauto.
Qed.

Definition meminit (C:Set) : { mem : (Memory C) | Memory_Valid C mem }.
Proof.
 unfold Memory_Valid.
 exists (1, (fun a => None)).
 intros a. simpl. auto.
Defined.
