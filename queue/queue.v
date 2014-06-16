Require Import Program.
Require Import Omega.

(* this is the state monad, fixed to just a single
   store element that is a pair of two lists of integers *)
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

Definition run_s {A : Set} : S A -> (A * ST) := 
  fun v => match v (nil,nil) with
             | (v,st) => (v,st)
           end.


Definition enq : nat -> S () := 
  fun n => 
    bind get
         (fun q =>
           match q with
             | (front,back) => set (cons n front,back)
           end).

Fixpoint rev_acc (l:list nat) acc :=
  match l with
    | nil => acc
    | (cons x ls) => rev_acc ls (cons x acc)
  end.

Definition rev l := rev_acc l nil.

Definition deq : S nat :=
  bind get
       (fun q => 
          match q with
            | (nil,nil) => ret 123 (* deq an empty queue; failure *)
            | (front,cons tl back) => 
              bind (set (front,back))
                   (fun _ => ret tl)
            | (cons hd front, nil) =>
              match rev (cons hd front) with
                | nil => ret 456  (* this can't happen .... *)
                | (cons tl back) =>
                  bind (set (nil,back))
                       (fun _ => ret tl)
                           end 
          end).

Example ex1 : run (bind (enq 1) (fun _ => deq)) = run (ret 1).
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
              = run (ret 2).
Proof.
  compute.
  reflexivity.
Qed.
