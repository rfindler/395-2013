Require Import Program.
Require Import Omega.
Require Import List.
Require Import Braun.common.util.

(* this is the type of things in the store *)
Definition Q := (list nat * list nat)%type.

(* this is the state type, a finite map from *)
(* addresses to pairs of two lists of        *)
(* integers, ie our queue's internal state   *)
Definition ST := ((nat -> Q) * nat)%type.

Definition STeq (st st':ST) :=
  (snd st) = (snd st') /\
  forall n, ((fst st) n) = ((fst st') n).

Definition CS
           (A:Set)
           (Pre : ST -> Prop)
           (Post: A -> ST -> ST -> nat -> Prop) : Set :=
  forall st:ST,
    Pre st ->
    {(a,st') : A * ST | exists an,
                          Post a st st' an}.
Hint Unfold CS.

Definition ret (A:Set) (a:A)
: CS A
     (fun st => True)
     (fun a' st st' time => st=st' /\ a=a' /\ time = 0).
Proof.
  intros st _.
  exists (a,st).
  exists 0.
  auto.
Defined.

(* START: bind *)
Definition bind 
           (A:Set) (B:Set)
           (A_Pre:ST -> Prop)
           (A_Post:A -> ST -> ST -> nat -> Prop)
           (B_Pre:A -> ST -> Prop)
           (B_Post:A -> B -> ST -> ST -> nat -> Prop)
           (A_impl_B_Pre:
             forall st0, 
               A_Pre st0 -> 
               forall a st1 an, 
                 A_Post a st0 st1 an -> 
                 B_Pre a st1)
           (am:CS A A_Pre A_Post)
           (bf:forall (a:A), CS B (B_Pre a) (B_Post a))
: CS B A_Pre
     (fun b st0 st2 n => exists a st1 an bn,
                           A_Post a st0 st1 an /\
                           B_Post a b st1 st2 bn /\
                           n = an+bn).
(* STOP: bind *)
Proof.
  intros st0 APRE.
  destruct (am st0 APRE) as [[a st1] A_PROP]; clear am.
  destruct (bf a st1) as [[b st2] B_PROP].
  destruct A_PROP as [an A_POST].
  apply (A_impl_B_Pre st0 APRE a st1 an A_POST).
  exists (b,st2).
  destruct A_PROP as [an A_POST].
  destruct B_PROP as [bn B_POST].
  exists (an+bn) a st1.
  exists an bn.
  repeat split; assumption.
Defined.

Definition inc 
           (A:Set)
           k
           (Pre:ST -> Prop)
           (Post:A -> ST -> ST -> nat -> Prop)
           (C : CS A Pre 
                   (fun a st st' time =>
                      forall time',
                        time' = time + k ->
                        Post a st st' time'))
: CS A Pre Post.
Proof.
  intros st PRE.
  destruct (C st PRE) as [[a st'] P].
  exists (a,st').
  destruct P as [an IMPL_POST].
  exists (an+k).
  apply IMPL_POST.
  reflexivity.
Defined.

Definition get : 
  forall addr, 
    CS Q 
       (fun st => True)
       (fun q st_pre st_post time =>
          time = 0 /\ ((fst st_post) addr) = q /\ st_pre = st_post).
Proof.
  intros addr [fm high_addr] _.
  exists (fm addr,(fm,high_addr)).
  exists 0.
  repeat split; reflexivity.
Defined.

Definition set:
  forall addr nv,
    CS ()
       (fun st => True)
       (fun q st_pre st_post time =>
          time = 0 /\
          (snd st_pre) = (snd st_post) /\
          ((fst st_post) addr) = nv /\ 
          forall addr', 
            (addr <> addr') -> 
            ((fst st_post) addr') = ((fst st_pre) addr')).
Proof.
  intros addr nv [fm high_addr] _.
  exists (tt,(fun addr' => if (eq_nat_dec addr addr') then nv else (fm addr'),high_addr)).
  exists 0.
  simpl.
  repeat split.
  destruct (eq_nat_dec addr addr);intuition.
  intros addr' NEQ.
  destruct (eq_nat_dec addr addr');intuition.
Defined.

Definition alloc : 
  CS nat 
     (fun st => True)
     (fun res st_pre st_post time =>
        time = 0 /\
        res = (snd st_pre) /\
        (snd st_post) = (snd st_pre)+1).
Proof.
  intros [fm high_addr] _.
  exists (high_addr,(fm,high_addr+1)).
  exists 0.
  repeat split; reflexivity.
Defined.

(* all allocated values are initialized as a pair of empty lists *)
Definition init_st : ST := (fun n => (nil,nil),0).

Definition run {A : Set} (Pre : ST -> Prop) Post : (Pre init_st) -> CS A Pre Post -> A.
Proof.
  intros PRE Computation.
  destruct (Computation init_st) as [[a _] _].
  apply PRE.
  apply a.
Defined.

Notation "<== x" := (ret _ x) (at level 55).
Notation "+= k ; c" := (inc _ k _ _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ _ _ _ _ y (fun (x : _) => z) )
                           (at level 30, right associativity).
Notation "! x" := (get x) (at level 55).
Notation "x ::== y ; z" := (bind _ _ _ _ _ _ _ (set x y) (fun _ => z)) 
                             (at level 30, right associativity).
