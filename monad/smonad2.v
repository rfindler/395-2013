Require Import Program.

Section monad.
Variable ST : Set.

Definition ST_Pre : Type
  := ST -> Prop.
Definition ST_Post (A:Set) : Type :=
  ST -> A -> ST -> Prop.
Definition C_Post (A:Set) : Type :=
  ST -> A -> nat -> ST -> Prop.

Program Definition
  CS (st_pre : ST_Pre) (A : Set) (st_post : ST_Post A)
     (c_post : C_Post A) : Set :=
  forall st : { st : ST | st_pre st },
    { (a, st') : A * ST | st_post st a st' /\
      (* xxx what if the proof requires knowing st_post? *)
      exists an, c_post st a an st' }.
Hint Unfold CS.

Definition top : ST_Pre := fun st => True.

Program Definition ret (A : Set) (c_post : C_Post A) 
  : forall av,
    (forall st, c_post st av 0 st) ->
    CS top A (fun st ap st' => st = st' /\ ap = av) c_post.
Proof.
  intros A c_post av CPav0.
  unfold CS.
  intros [st st_pre_st].
  exists (av, st).
  eauto.
Defined.

Program Definition bind:
  forall (A B:Set)
    (st_preA : ST_Pre) (st_preB : A -> ST_Pre)
    (st_postA : ST_Post A) (st_postB : A -> ST_Post B)
    (c_postA : C_Post A) (c_postB : C_Post B),
    (CS st_preA A st_postA c_postA) ->
    (forall (a : A), (* xxx missing (pa:exists an, PA a an) from monad.v *)
      (CS (st_preB a) B (st_postB a)
        (fun stA b bn stB =>
          forall st0 an,
            c_postA st0 a an stA ->
            c_postB st0 b (an+bn) stB))) ->
    CS (fun st0 =>
      st_preA st0 /\
      (forall a stA,
        st_postA st0 a stA ->
        st_preB a stA))
    B
    (fun st0 b stB =>
      exists a, exists stA,
        st_postA st0 a stA /\
        st_postB a stA b stB)
    c_postB.
Proof.
  intros. rename H into am. rename H0 into bf.
  intros [st0 [st_preA_st0 st_postApreB]].
  edestruct (am (exist st_preA st0 st_preA_st0))
   as [[av stA] [st_postA_stA c_postA_stA]].
  simpl in st_postA_stA.
  assert (st_preB av stA) as st_preB_stA. eauto.
  edestruct (bf av (exist (st_preB av) stA st_preB_stA)) as
    [[bv stB] [st_postB_stB c_postApostB_stB]].
  simpl in st_postB_stB.
  exists (bv, stB).
  split. exists av. exists stA. split.
  simpl. auto. auto.

  destruct c_postA_stA as [an c_postA_stA].
  destruct c_postApostB_stB as [bn c_postApostB_stB].
  exists (an + bn). eauto.
Defined.

Program Definition get:
  CS top ST (fun st0 st1 st2 => st0 = st1 /\ st1 = st2)
  (fun _ st1 st1n _ => st1n = 0).
Proof.
  intros [st0 st_pre_st0].
  exists (st0, st0). simpl.
  eauto.
Defined.

Program Definition put (st2:ST) :
  CS top () (fun _ _ st2' => st2 = st2')
  (fun _ _ un _ => un = 0).
Proof.
  intros st2 [st0 st_pre_st0].
  exists ((), st2).
  eauto.
Defined.

Program Definition inc (k:nat) :
  forall (st_pre : ST_Pre) (A:Set) (st_post : ST_Post A) (c_post : C_Post A),
    CS st_pre A st_post
    (fun st a an st' =>
      forall am,
        an + k = am ->
        c_post st a am st') ->
    CS st_pre A st_post c_post.
Proof.
  intros. rename H into am.
  intros [st0 st_pre_st0]. simpl.
  edestruct (am (exist st_pre st0 st_pre_st0))
   as [[av stA] [st_post_stA c_post_stA]].
  simpl in *.
  exists (av, stA).
  split. auto.
  destruct c_post_stA as [an c_post_stA].
  exists (an + k).
  eapply c_post_stA.
  auto.
Defined.

End monad.
    
(* xxx example inline for testing *)
Section dumb_list.

Definition ST := list nat.

Program Fixpoint list_insert x (l:ST) : ST :=
  match l with
    | nil =>
      cons x nil
    | cons y l =>
      cons y (list_insert x l)
  end.

Program Definition insert (x:nat) :
  @CS ST
  (fun st => True)
  ()
  (fun st _ st' => st' = list_insert x st)
  (fun st _ n st' => n = length st)
  :=
  @bind ST ST ()
  (fun st => True)
  (fun st0v st0 => st0v = st0)
  (fun st0 st1 st2 => st0 = st1 /\ st1 = st2)
  (fun st0v st0 _ st2 => st2 = list_insert x st0)
  (fun st0 st0v getn st1 => getn = 0)
  (fun st0 _ putn st2 => putn = length st0)
  (@get ST)
  (fun l =>
    (@put ST (list_insert x l))).

Next Obligation.
  unfold top. auto.
Defined.

Next Obligation.
  rename x0 into st0.
  split. auto.

  (* XXX *)
  exists (length st
  
  eauto.
  
  destruct (`
       (put ST (list_insert x st0)
          (exist (fun st : ST => top ST st) st0
             (insert_obligation_1 x st0
                (exist (fun st : ST => st0 = st) st0 eq_refl))))) as [u st1].
  
  split.
 simpl.

End dumb_list.

