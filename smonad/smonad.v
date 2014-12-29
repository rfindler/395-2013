Require Import Program.

Definition CS_Pre (ST:Set) : Type
  := ST -> Prop.
Hint Unfold CS_Pre.

Definition CS_Post (ST:Set) (A:Set) : Type :=
  ST -> A -> nat -> ST -> Prop.
Hint Unfold CS_Post.

Definition CS_Result (ST:Set) (A : Set) (st:ST) (post : CS_Post ST A) :=
  { (a, st') : A * ST |
    (* cs final *)
    exists an, post st a an st' }.
Hint Unfold CS_Result.

Definition
  CS (ST:Set) (pre : CS_Pre ST) (A : Set) (post : CS_Post ST A) : Set :=
  forall st : ST,
    pre st ->
    CS_Result ST A st post.
Hint Unfold CS.

Program Definition weaken (ST:Set)
  (pre : CS_Pre ST) (pre' : CS_Pre ST)
  (A:Set)  
  (post : CS_Post ST A) (post' : CS_Post ST A)
  (am:CS ST pre A post)
  (pre_stronger : (forall st, pre' st -> pre st))
  (post_weaker :
    (forall st a an st',
      post st a an st' ->
      post' st a an st')) :
  (CS ST pre' A post').
Proof.
  intros.
  intros st pre_st.
  edestruct (am st) as [[a st'] post_st'].
  auto.
  exists (a, st').
  destruct post_st' as [an post_st'].
  eauto.
Defined.

Definition top (ST:Set) : CS_Pre ST := fun st => True.
Hint Unfold top.

Program Definition ret (ST:Set) (A : Set) (post : CS_Post ST A) 
  : forall av,
    (forall st, post st av 0 st) ->
    CS ST (top ST) A (fun st ap an st' => st = st' /\ ap = av /\ post st ap an st').
Proof.
  intros ST A post av CPav0.
  unfold CS.
  intros st pre_st.
  exists (av, st).
  eauto.
Defined.
Hint Unfold ret.

Program Definition bind:
  forall (ST:Set) (A:Set)
    (preA : CS_Pre ST) (postA : CS_Post ST A) (am:(CS ST preA A postA))
    (B:Set) (preB : A -> nat -> CS_Pre ST) (postB : A -> CS_Post ST B)
    (bf:(forall (a : A) (postA_stA : (exists st an stA, postA st a an stA)),
      (CS
        ST
        (* bf pre *)
        (fun stA =>
          exists st an,
            postA st a an stA /\
            preB a an stA)
        B
        (* bf post *)
        (fun stA bv bn stB =>
          forall an,
            preB a an stA ->
            postB a stA bv (an+bn) stB)))),
    CS ST
    (* bind pre *)
    (fun st0 =>
      preA st0 /\
      (forall a an stA,
        postA st0 a an stA ->
        preB a an stA))
    B
    (fun st0 b cn stB =>
      exists a an stA bn,
        cn = an + bn /\
        postA st0 a an stA /\
        postB a stA b cn stB).
Proof.
  intros.
  intros st0 [preA_st0 postApreB].
  edestruct (am st0 preA_st0)
   as [[av stA] postA_stA].
  simpl in *.

  assert (exists st an stA, postA st av an stA) as epostA_stA.
  destruct postA_stA. eauto.

  edestruct
  (bf av epostA_stA stA)
  as [[bv stB] postApostB_stB].

  destruct postA_stA. eauto.

  clear epostA_stA.
  exists (bv, stB).
  destruct postA_stA as [an postA_stA].
  destruct postApostB_stB as [bn postB_stB].
  simpl in *.
  exists (an + bn). exists av.
  exists an. exists stA.
  exists bn. eauto.
Defined.
Hint Unfold bind.

Program Definition get (ST:Set):
  CS ST (top ST) ST (fun st0 st1 gn st2 => st0 = st1 /\ gn = 0 /\ st2 = st0).
Proof.
  intros ST.
  intros st0 pre_st0.
  exists (st0, st0). simpl.
  eauto.
Defined.
Hint Unfold get.

Program Definition put (ST:Set) (st2:ST) :
  CS ST (top ST) () (fun _ _ pn st2' => pn = 0 /\ st2 = st2').
Proof.
  intros ST st2 st0 pre_st0.
  exists ((), st2).
  eauto.
Defined.
Hint Unfold put.

Program Definition inc (ST:Set) (k:nat) :
  forall (pre : CS_Pre ST) (A:Set) (post : CS_Post ST A),
    CS ST pre A 
    (fun st a an st' =>
      forall am,
        an + k = am ->
        post st a am st') ->
    CS ST pre A post.
Proof.
  intros. rename H into am.
  intros st0 pre_st0. simpl.
  edestruct (am st0 pre_st0)
   as [[av stA] post_stA].
  simpl in *.
  exists (av, stA).
  destruct post_stA as [an post_stA].
  exists (an + k). eauto.
Defined.
Hint Unfold inc.

(* Wrap everything in weaken unless it is the first argument to
   bind. *)
