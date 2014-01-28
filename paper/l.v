Require Import Arith Omega Braun.common.util.
Require Import Coq.Logic.JMeq Coq.Program.Wf.

Section l.

  Variable A:Set.

  (* START: list *)
  Inductive list : Type :=
  | empty : list
  | cons (hd : A) (tl : list) : list.
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
  Inductive list_len : list -> nat -> Type :=
  | L_empty : list_len empty 0
  | L_cons (tl_len : nat)
           (hd : A)
           (tl : list)
           (tl_ok : list_len tl tl_len) 
    : list_len (cons hd tl) (tl_len + 1).
  (* STOP: list_has_len *)

  Lemma drop_zero : forall l, drop 0 l = l.
  Proof.
    intros l.
    destruct l; simpl; reflexivity.
  Qed.

  Lemma drop_empty : forall n, drop n empty = empty.
  Proof.
    induction n; simpl; reflexivity.
  Qed.

  Lemma drop_non_empty_non_zero : 
    forall n hd tl,
      drop (S n) (cons hd tl) = drop n tl.
  Proof.
    intros n hd tl.
    simpl.
    replace (n-0) with n; try omega.
    reflexivity.
  Qed.

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
    intros n. induction n.
    intros len l LLen.
    simpl.
    rewrite drop_zero.
    replace (len-0) with len; try omega.
    assumption.

    intros len l.
    induction 1.

    rewrite drop_empty.
    simpl.
    constructor.

    rewrite drop_non_empty_non_zero.
    remember (IHn tl_len tl H) as IH; clear HeqIH.
    dispatch_if x x'.

    assert ((if le_dec n tl_len then tl_len - n else 0) = tl_len + 1 - S n) as IFS;
      [dispatch_if y y'; omega |
       rewrite <- IFS; assumption].

    replace (if le_dec n tl_len then tl_len - n else 0) with 0 in IH.
    assumption.

    dispatch_if z z'; omega.
  Qed.
  
End l.

(*
Recursive Extraction drop.
*)