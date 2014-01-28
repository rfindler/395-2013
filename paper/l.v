Require Import Arith Omega Braun.common.util.
Require Import Coq.Logic.JMeq Coq.Program.Wf.

Section l.

  Variable A:Set.

  (* START: list *)
  Inductive list : Set :=
  | empty : list
  | cons (hd : A)
         (tl : list)
    : list.
  (* STOP: list *)

  (* START: drop *)
  Fixpoint drop (n : nat) (l : list) : list
    := if zerop n
       then l
       else
         match l with
           | empty => empty
           | (cons hd tl) => 
             drop (n-1) tl
         end.
  (* STOP: drop *)
  
  (* START: list_has_len *)
  Inductive list_len : list -> nat -> Set :=
  | L_empty : list_len empty 0
  | L_cons (tl_len : nat)
           (hd : A)
           (tl : list)
           (tl_ok : list_len tl tl_len) 
    : list_len (cons hd tl) (tl_len + 1).
  (* STOP: list_has_len *)

  (* START: drop_lengths *) 
  Theorem drop_lengths :
    forall n len l,
           list_len l len ->
           list_len (drop n l)
                    (if (le_dec n len)
                     then (len - n)
                     else 0).
  (* STOP: drop_lengths *) 
  Proof.
    intros.
    induction H.
    simpl.
    dispatch_if T T'; dispatch_if T2 T2'; constructor.

    simpl.
    dispatch_if T T'; dispatch_if T2 T2'.
    subst n.
    replace (tl_len + 1 - 0) with (tl_len + 1); try omega.
    constructor.
    assumption.

    unfold not in T2'.
    subst.
    assert False; intuition.

    destruct n. assert False; intuition.
    clear T'.
    replace (S n - 1) with n; try omega.
    replace (tl_len+1-S n) with (tl_len - n); try omega.
    
    replace (if le_dec (S n) tl_len then tl_len - S n else 0)
    with (tl_len - S n) in IHlist_len; [| dispatch_if T3 T3'; omega].

    admit.
    admit.
  Qed.
  
End l.
