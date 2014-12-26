Require Import Braun.smonad.smonad.

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

Program Definition alloc (C:Set) (init:C) :
  (CS (Memory C) (fun mem => Memory_Valid C mem) Addr
    (fun mem next allocn mem' =>
      next = (mem_next C mem) /\
      allocn = 0 /\
      Memory_Extends C mem next init mem'))
  :=
  (@weaken _ _ _ _ _ _
    (@bind _ _ _ _ (@get _)
      _
      (fun memv memn mem =>
        Memory_Valid C mem /\
        memv = mem /\
        memn = 0)
      (fun memv mem next allocn mem' =>
        memv = mem /\
        next = mem_next C mem /\
        allocn = 0 /\
        Memory_Extends C mem next init mem')
      (fun mem pmem =>
        match mem with
          (next, map) =>
          (@weaken _ _ _ _ _ _
            (@bind _ _ _ _ (@put _ (addr_inc next, map_ext C map next init))
              _
              (fun _ putn mem' =>
                putn = 0)
              (fun _ mem retv retn mem' =>
                retv = next /\
                retn = 0 /\
                mem' = mem)
              (fun _ p_ =>
                (@weaken _ _ _ _ _ _
                  (@ret _ _
                    (fun mem r rn mem' =>
                      r = next /\
                      rn = 0 /\
                      mem' = mem)
                    next _) _ _))) _ _)
        end)) _ _).

Solve Obligations using auto.
Solve Obligations using intuition.

Next Obligation.
  intros.
  subst mem.
  rename H0 into P.
  destruct P as [MV [EQst EQan0]].
  subst st an0.
  clear pmem.
  destruct H as [tt [an0 [stA [bn [EQan [[EQan0 EQstA] [EQa [EQan' EQst']]]]]]]].
  subst an an0 stA a st'.
  clear tt.
  replace bn with 0 in *. clear EQan' bn.
  unfold Memory_Extends.
  unfold Memory_Valid in *.
  simpl in *.
  repeat split; eauto.

  intros a LE.
  unfold addr_inc in *.
  eapply map_ext_none.
  eapply MV. omega. omega.
Defined.

(* XXX There is clearly a tactic here. *)
Next Obligation.
  intros. split; auto.
  intros.
  rename H0 into P.
  destruct P as [EQ1 [EQ2 EQ3]].
  subst st an stA.
  auto.
Defined.

Next Obligation.
  intros. repeat destruct H.
  repeat destruct H0.
  repeat destruct H.
  destruct H0. destruct H1.
  destruct H2.
  subst. auto.
Defined.

Program Definition ref (C:Set) (a:Addr) :
  (CS (Memory C) (fun mem => True) (option C)
    (fun mem av refn mem' =>
      av = mem_map C mem a /\
      refn = 0 /\
      mem' = mem))
  :=
  (@weaken _ _ _ _ _ _
    (@bind _ _ _ _ (@get _)
      _
      (fun gv gn mem =>
        gv = mem /\
        gn = 0)
      (fun gv mem av refn mem' =>
        gv = mem /\
        av = mem_map C mem a /\
        refn = 0 /\
        mem' = mem)
      (fun memv pmem =>
        (@weaken _ _ _ _ _ _
          (@ret _ _
            (fun mem r rn mem' =>
              r = mem_map C memv a /\
              rn = 0 /\
              mem' = mem)
            (mem_map C memv a) _) _ _))) _ _).

Solve Obligations using auto.

Next Obligation.
  intros.
  destruct H as [EQst [EQa0 [EQa02 [EQan EQst']]]].
  subst st' a0 an.
  clear EQst' EQa02.
  destruct H0 as [EQst EQan0].
  subst st an0.
  auto.
Defined.

Next Obligation.
  intros.
  split; auto.
  intros.
  destruct H0. destruct H1.
  subst.
  auto.
Defined.

Next Obligation.
  intros.
  destruct H as [a1 [an0 [stA [bn [EQan [[EQst [EQan0 EQstA]] [EQa1 [EQa0 [EQan2 EQst']]]]]]]]].
  subst an a1 an0 stA st'.
  auto.
Defined.

(* The other two can be done this simply too... *)
Program Definition setmem (C:Set) (a:Addr) (av':C) :
  (CS (Memory C) (fun mem => True) ()
    (fun mem _ setn mem' =>
      setn = 0 /\
      Memory_Modifies C mem a av' mem')).
Proof.
  intros C a av' mem P.
  destruct mem as [next map].
  exists ((), (next, map_ext C map a av')).
  exists 0. split. auto.
  unfold Memory_Modifies.
  simpl.
  repeat split; eauto.
  intros a'.
  destruct (addr_eq_dec a a'); eauto.
Defined.

Program Fixpoint memory_reverse : nat.
