Require Import braun insert.
Require Import Div2 List.
Require Import Arith Arith.Even Arith.Div2.
Set Implicit Arguments.

Section ilist.
  Variable A : Set.
  Variable P : nat -> Set.

  Inductive ilist : nat -> Set :=
  | Nil  : ilist 0
  | Cons : forall n, A -> ilist n -> ilist (S n).
End ilist.

Section ifoldr.
  Variables A : Set.
  Variable B : nat -> Set.
  Variable f : forall n, A -> B n -> B (S n).
  Variable i : B 0.

  Fixpoint ifoldr n (ls : ilist A n) : B n :=
    match ls with
      | Nil => i
      | Cons _ x ls' => f x (ifoldr ls')
    end.
End ifoldr.

Section make_array_naive.
  Variable A : Set.

  Program Definition make_array_naive n (s : ilist A n) : braun_tree A n :=
    ifoldr (fun n => braun_tree A n)
           (fun n x t => insert x t)
           Empty
           s.
  Obligation 1. omega. Qed.

End make_array_naive.

Section make_array_naive'.
  Variable A : Set.

  Definition sep (n : nat) : nat * nat :=
    let d := div2 n in
    if even_odd_dec n
    then (d, d)
    else (S d, d).

  Definition unravel_type n : Set :=
    let '(l, r) := sep n in
    prod (ilist A l) (ilist A r).

  Eval compute in unravel_type 17.
  Check ifoldr.

  (* Broken here, Program can't do non-inductive types?
     Using refine gives you exactly the error you'd expect.
   *)
  Program Definition unravel n (l : ilist A n) : unravel_type n :=
    (ifoldr (fun n => unravel_type n)
            (fun _ h o_e =>
               let '(o, e) := o_e in
               (Cons _ h e, o))
            (Nil, Nil)
            l).
  
    match l with
      | Nil => (_, _)
      | Cons _ h t =>
        let '(o,e) := unravel t in
        (Cons _ h e, o)
    end.

(* This probably needs a refine
  Fixpoint unravel' (n : nat) (s : ilist A n) : ilist A (div2_ceil n) * ilist A (div2 n) :=
    match s with
      | Nil => (Nil, Nil)
      | Cons n h t => let (o,e) := unravel t in (cons h e, o)
    end.
*)

(* Not type checking since s isn't a length-indexed list. 
   That said, it would probably be easy if unravel' worked.
  Fixpoint make_array_n' (s : list A) : braun_tree A (length s) :=
    match s with
      | nil => Empty
      | cons h t => let (o,e) := unravel t in 
                    Node h _ _ _ (make_array_n' o) (make_array_n' e)
    end.
*)
(* Inverse of above function for fun *)
  Fixpoint ravel (s1 s2 : list A) : list A :=
    match s1, s2 with
      | nil, _ => s2
      | _, nil => s1
      | cons h1 t1, cons h2 t2 => cons h1 (cons h2 (ravel t1 t2))
    end.

  Fixpoint unmake_array_n' n (bt : braun_tree A n) : list A :=
    match bt with
      | Empty => nil
      | Node h _ _ _ s t => cons h (ravel (unmake_array_n' s) (unmake_array_n' t))
    end.

End make_array_naive'.

Section make_array.
  Variable A : Type.
(* Can't guess decreasing argument of fix. 
   Haven't worked on this as much, but the decreasing argument here is obviously the length of the list.
   That being said, this makearray definition won't work unless I can get fold to work *)


  Fixpoint rows (k : nat) (xs : list A) : list (nat * (list A)) :=
    match xs with
      | nil => nil
      | _ => (cons (k, firstn k xs) (rows (2*k) (skipn k xs)))
    end.
  
End make_array.
