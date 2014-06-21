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

Definition S (A:Set) := ST -> (A * ST).

Definition ret {A: Set} (a:A) : S A := (fun st => (a,st)).

Definition bind {A : Set} {B : Set} : (S A) -> (A -> S B) -> S B :=
  fun ov f =>
    fun st => 
      match (ov st) with
        | (a, st') => ((f a) st') 
      end.

Definition get : nat -> S Q := 
  fun addr st => ((fst st) addr,st).
Definition set : nat -> Q -> S () := 
  fun addr new_q => 
    fun old_st => 
      ((),
       (fun addr' => if eq_nat_dec addr addr' 
                     then new_q 
                     else (fst old_st) addr',
        snd old_st)).
Definition alloc : S nat :=
  fun st =>
    (snd st,(fst st,snd st+1)).

(* all allocated values are initialized as a pair of empty lists *)
Definition init_st : ST := (fun n => (nil,nil),0).

Definition run {A : Set} : S A -> A := 
  fun v => match v init_st with
             | (v,st) => v
           end.

(* given a computation and some interesting addresses, 
   runs the computation and extracts the interesting store values,
   returning them as lists in the order the queue would return them. *)
Definition run_s {A : Set} : S A -> (list nat) -> (A * list (list nat)) := 
  fun v addrs => match v init_st with
                   | (v,(st,addr)) => 
                     (v, map (fun addr => match st addr with
                                            | (l1,l2) => l2 ++ rev' l1
                                          end)
                             addrs)
                 end.

Definition enq : nat -> nat -> S () := 
  fun addr n => 
    bind (get addr)
         (fun q =>
           match q with
             | (front,back) => set addr (cons n front,back)
           end).

Definition deq : nat -> S (option nat) :=
  fun addr =>
    bind (get addr)
         (fun q => 
            match q with
              | (nil,nil) => ret None
              | (front,cons back more) => 
                bind (set addr (front,more))
                     (fun _ => ret (Some back))
              | (cons front more, nil) =>
                match rev' (cons front more) with
                  | nil => ret None (* can't happen *)
                  | (cons back more') =>
                    bind (set addr (nil,more'))
                         (fun _ => ret (Some back))
                end 
            end).

Example ex1 : run (bind alloc (fun addr => (bind (enq addr 1) (fun _ => (deq addr)))))
              = run (ret (Some 1)).
Proof.
  compute.
  reflexivity.
Qed.

Example ex2 : run (bind alloc
                        (fun addr =>
                           bind (enq addr 1) 
                                (fun _ =>
                                   bind (enq addr 2)
                                        (fun _ =>
                                           bind (deq addr)
                                                (fun _ => (deq addr))))))
              = run (ret (Some 2)).
Proof.
  compute.
  reflexivity.
Qed.

Theorem enq_correct : 
  forall l1 l2 n addr,
    run_s (bind (set addr (l1,l2))
                (fun _ => (enq addr n)))
          [addr]
         = ((), [l2 ++ rev' l1 ++ [n]]).
Proof.
  unfold enq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  intros l1 l2 n addr.
  simpl.
  dispatch_if X1 X1';[|intuition].
  dispatch_if X2 X2';[|intuition].
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
  forall l1 l2 addr,
    run_s (bind (set addr (l1,l2))
                (fun _ => deq addr))
          [addr]
    = match (l2 ++ rev' l1) with
        | [] => (None, [nil])
        | (x :: xs) => (Some x, [xs])
      end.
Proof.
  intros l1 l2 addr.
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
  dispatch_if X X';intuition.
  dispatch_if Y Y';intuition.

  (* queue nonempty *)

  destruct l2.

  destruct l1.
  simpl.
  compute.
  dispatch_if X X';intuition.
  dispatch_if Y Y';intuition.

  (* back of queue is empty *)
  unfold deq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  simpl.
  dispatch_if X X';[clear X|intuition].

  remember (rev' (n0::l1)) as LST.
  destruct LST.
  assert False;[|intuition].
  apply (nonempty_rev_nonempty n0 l1).
  auto.

  dispatch_if X X';[clear X|intuition].

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

  dispatch_if X X';[clear X|intuition].

  destruct l1; (dispatch_if X X';[clear X|intuition]); auto.
Qed.
