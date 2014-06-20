Require Import Program.
Require Import Omega.
Require Import List.
Require Import Braun.common.util.

(* this is the state monad, fixed to just a single
   store element that is a pair of two lists of 
   integers, ie our queue's internal state *)
Definition ST := (list nat * list nat)%type.

Definition S (A:Set) := ST -> (A * ST).

Definition ret {A: Set} (a:A) : S A := (fun st => (a,st)).

Definition bind {A : Set} {B : Set} : (S A) -> (A -> S B) -> S B :=
  fun ov f =>
    fun st => 
      match (ov st) with
        | (a, st') => ((f a) st') 
      end.

Definition get : S ST := fun st => (st,st).
Definition set : ST -> S () := fun new => fun old => ((),new).

Definition run {A : Set} : S A -> A := 
  fun v => match v (nil,nil) with
             | (v,st) => v
           end.

(* returns the queue in list order after the end 
   of the monadic computation, in addition to 
   returning the result of the monadic computation *)
Definition run_s {A : Set} : S A -> (A * list nat) := 
  fun v => match v (nil,nil) with
             | (v,(l1,l2)) => (v, l2 ++ rev' l1)
           end.

Definition enq : nat -> S () := 
  fun n => 
    bind get
         (fun q =>
           match q with
             | (front,back) => set (cons n front,back)
           end).

Definition deq : S (option nat) :=
  bind get
       (fun q => 
          match q with
            | (nil,nil) => ret None
            | (front,cons back more) => 
              bind (set (front,more))
                   (fun _ => ret (Some back))
            | (cons front more, nil) =>
              match rev' (cons front more) with
                | nil => ret None (* can't happen *)
                | (cons back more') =>
                  bind (set (nil,more'))
                       (fun _ => ret (Some back))
                           end 
          end).

Example ex1 : run (bind (enq 1) (fun _ => deq)) = run (ret (Some 1)).
Proof.
  compute.
  reflexivity.
Qed.

Example ex2 : run (bind (enq 1) 
                        (fun _ =>
                           bind (enq 2)
                                (fun _ =>
                                   bind deq 
                                        (fun _ => deq))))
              = run (ret (Some 2)).
Proof.
  compute.
  reflexivity.
Qed.

Theorem enq_correct : 
  forall l1 l2 n,
    run_s (bind (set (l1,l2))
                (fun _ => (enq n)))
         = ((), l2 ++ rev' l1 ++ [n]).
Proof.
  unfold enq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  intros l1 l2 n.
  replace (rev' (n::l1)) with (rev (n::l1));
    [| unfold rev' ; rewrite rev_alt; auto].
  simpl.
  replace (rev l1) with (rev' l1);
    [| unfold rev' ; rewrite rev_alt; auto].
  auto.
Qed.

Lemma nonempty_rev_nonempty : forall (x:nat) xs, [] = rev' (x :: xs) -> False.
  intros x xs BAD.
  unfold rev' in BAD.
  rewrite <- rev_alt in BAD.
  assert (length (nil:list nat) = length (rev (x :: xs))) as BAD_LEN;
    [rewrite BAD;reflexivity|clear BAD].
  rewrite rev_length in BAD_LEN.
  simpl in BAD_LEN.
  intuition.
Qed.

Theorem deq_correct : 
  forall l1 l2,
    run_s (bind (set (l1,l2))
                (fun _ => deq))
    = match (l2 ++ rev' l1) with
        | [] => (None, nil)
        | (x :: xs) => (Some x, xs)
      end.
Proof.
  intros l1 l2.
  remember (app l1 (rev' l2)) as STATE.
  destruct STATE.

  (* queue is empty *)
  symmetry in HeqSTATE.
  apply app_eq_nil in HeqSTATE.
  destruct HeqSTATE.
  subst l1.
  assert (l2 = []).
  destruct l2.
  reflexivity.
  assert False;[|intuition]. 
  apply (nonempty_rev_nonempty n l2).
  auto.
  subst l2.
  compute.
  reflexivity.

  (* queue nonempty *)

  destruct l2.

  destruct l1; auto.

  (* back of queue is empty *)
  unfold deq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  simpl.

  remember (rev' (n0::l1)) as LST.
  destruct LST.
  assert False;[|intuition].
  apply (nonempty_rev_nonempty n0 l1).
  auto.

  unfold rev'.
  simpl.
  rewrite app_nil_r.
  reflexivity.

  (* back of queue isn't empty *)
  unfold deq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  simpl.

  destruct l1; auto.
Qed.
