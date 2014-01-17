Require Import Braun.tmonad.monad.

Require Import Braun.logical.sequence.

Require Import Arith.Minus.

Set Implicit Arguments.

Section take_drop.

  Variable A : Set. 
  Check min.
  Program Fixpoint take (k : nat) (l : list A) : {! hds !:! list A
                                                    !<! c !>!
                                                    length hds = min k (length l)
                                                  /\ c = length hds !} :=
    match k with 
        0   => nil
      | S n => 
        match l with
            nil => nil
          | cons x xs => 
            cons x (take n xs)
        end
    end.
  Obligations.
  Next Obligation.
  Proof.
    exists 0; auto.
  Qed.
  Next Obligation.
  Proof.
    exists 0; auto.
  Qed.
  Next Obligation.
  Proof.
    exists (S (length x0)); auto.
  Defined.

  Program Fixpoint drop (k : nat) (l : list A) : {! tls !:! list A 
                                                      !<! c !>!
                                                      length tls = (length l) - k
                                                    /\ c = length tls
                                                                  !} :=
    match k with
      | 0 => l
      | S n =>
        match l with 
          | nil => nil
          | cons _ xs =>
            drop n xs
        end 
    end.
  Obligations.
  Next Obligation.
  Proof.
    exists (length l); omega.
  Qed.
  Next Obligation.
  Proof.
    exists 0; auto.
  Qed.
End take_drop.

(* Cannot guess decreasing arg of fix *)
(* Program Fixpoint rows (A : Set) (k : nat) (l : list A) : {! rs !:! list (nat * list A)  *)
(*                                                             !<! c !>! *)
(*                                                             True *)
(*                                                             !} := *)
(*   match l with  *)
(*     | nil => <== nil *)
(*     | _ => *)
(*       front <- take k l; *)
(*         back <- (drop k l); *)
(*         tl <- rows (k + k) back; *)
(*         <== cons (k, front) tl *)
(*   end. *)
