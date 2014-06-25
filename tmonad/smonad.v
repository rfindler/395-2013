Require Import Program.
Require Import Omega.
Require Import List.
Require Import Braun.common.util.

(* this is the type of things in the store *)
Definition Q := (list nat * list nat)%type.

(* this is the state type, a finite map from
   addresses to pairs of two lists of 
   integers, ie our queue's internal state *)
Definition ST := ((nat -> Q) * nat)%type.

Definition CS 
           (A:Set)
           (Pre : ST -> nat -> Prop) 
           (Post: A -> ST -> ST -> nat -> Prop) : Set :=
  forall st:ST,
    {(a,st') : A * ST | forall pren, 
                          Pre st pren -> 
                          exists an,
                            Post a st st' (pren + an)}.
Hint Unfold CS.

Definition ret (A:Set)
               (Pre:ST -> nat -> Prop)
               (Post:A -> ST -> ST -> nat -> Prop)
               (a:A)
               (nosteps:forall st n, Pre st n -> Post a st st n)
: CS A Pre Post.
Proof.
  intros st.
  exists (a,st).
  intros pren pre_st0.
  exists 0.
  rewrite plus_0_r.
  auto.
Defined.

(* START: bind *)
Definition bind 
           (A:Set) (B:Set)
           (A_Pre:ST -> nat -> Prop)
           (A_Post:A -> ST -> ST -> nat -> Prop)
           (B_Pre:A -> ST -> nat -> Prop)
           (B_Post:A -> B -> ST -> ST -> nat -> Prop)
           (am:CS A A_Pre A_Post)
           (bf:forall (a:A), CS B (B_Pre a) (B_Post a))
: CS B 
     (fun st n => A_Pre st n /\ forall a st' an, A_Post a st st' an -> B_Pre a st' an)
     (fun b st0 st2 n => exists a st1 bn, A_Post a st0 st1 n /\ B_Post a b st1 st2 (n+bn)).
(* STOP: bind *)
Proof.
  intros st0.

  (* computation part *)
  destruct (am st0) as [[a st1] A_PROP]; clear am.
  destruct (bf a st1) as [[b st2] B_PROP]; clear bf.
  exists (b,st2).

  (* proof obligations part *)
  intros pren [A_PRE A_POST_TO_B_PRE].
  destruct (A_PROP pren A_PRE) as [an INT]; clear A_PROP A_PRE.
  destruct (B_PROP (pren+an) (A_POST_TO_B_PRE a st1 (pren + an) INT)) as [bn POST].
  exists an a st1 bn.
  split;assumption.
Defined.

Definition inc 
           k
           (Pre:ST -> nat -> Prop)
           (Post:() -> ST -> ST -> nat -> Prop)
           (ksteps:forall st n, Pre st n -> Post () st st (n+k))
: CS () Pre Post.
Proof.
  intros st.
  exists ((),st).
  intros pren PRE.
  exists k.
  apply ksteps.
  assumption.
Qed.

Definition get : 
  forall addr, 
    CS Q 
       (fun st n => True)
       (fun q st_pre st_post n => ((fst st_post) addr) = q /\ st_pre = st_post).
Proof.
  intros addr [fm high_addr].
  exists (fm addr,(fm,high_addr)).
  intros gt _.
  exists gt.
  split; reflexivity.
Defined.

Definition set:
  forall addr nv,
    CS ()
       (fun st n => True)
       (fun q st_pre st_post n =>
          (snd st_pre) = (snd st_post) /\
          ((fst st_post) addr) = nv /\ 
          forall addr', 
            (addr <> addr') -> 
            ((fst st_post) addr') = ((fst st_pre) addr')).
Proof.
  intros addr nv [fm high_addr].
  exists (tt,(fun addr' => if (eq_nat_dec addr addr') then nv else (fm addr'),high_addr)).
  intros t _.
  exists t.
  simpl.
  repeat split.
  destruct (eq_nat_dec addr addr);intuition.
  intros addr' NEQ.
  destruct (eq_nat_dec addr addr');intuition.
Defined.

Definition alloc : 
  CS nat 
     (fun st n => True)
     (fun res st_pre st_post n =>
        res = (snd st_pre) /\
        (snd st_post) = (snd st_pre)+1).
Proof.
  intros [fm high_addr].
  exists (high_addr,(fm,high_addr+1)).
  intros t _.
  exists t.
  split; reflexivity.
Defined.

(* all allocated values are initialized as a pair of empty lists *)
Definition init_st : ST := (fun n => (nil,nil),0).

Definition run {A : Set} Pre Post : CS A Pre Post -> A.
Proof.
  intros Computation.
  destruct (Computation init_st) as [[a _] _].
  apply a.
Defined.
