Set Implicit Arguments.

Require Import Program.

Definition C (A:Set) (P:A -> nat -> Prop) : Set := {a | exists n, (P a n)}.
Hint Unfold C.

Definition ret (A:Set) (PA:A -> nat -> Prop) (x:A) (PAx:PA x 0) : @C A PA.
Proof.
  eauto.
Defined.

Definition bind0 (A:Set) (B:Set) (PA:A -> nat -> Prop) (PB:B -> nat -> Prop)
           (xn:@C A PA) (yf:A -> @C B PB)
           (PBA:forall x xn y yn, (PA x xn) -> (PB y yn) -> (PB y (xn + yn)))
: @C B PB.
Proof.
  destruct xn as [x Px].
  edestruct yf as [y Py].
  apply x.
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply PBA;
  eauto.
Defined.

Definition bind1 (A:Set) (B:Set) (PA:A -> nat -> Prop) (PBi:B -> nat -> Prop) 
           (PB:B -> nat -> Prop)
           (xn:@C A PA) (yf:A -> @C B PBi)
           (PBA:forall x xn y yn, (PA x xn) -> (PBi y yn) -> (PB y (xn + yn)))
: @C B PB.
Proof.
  destruct xn as [x Px].
  edestruct yf as [y Py].
  apply x.
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply PBA;
  eauto.
Defined.

Definition inc (A:Set) PA (k:nat) (x:@C A (fun x xn => PA x (xn+k)))
: @C A PA.
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  eauto.
Defined.

Extraction Implicit inc [k].
Recursive Extraction ret bind0 bind1 inc.

(*
Notation "x >>= y" := (bind x y) (at level 55).
Notation "x >> y" := (bind x (fun _ => y)) (at level 30, right associativity).
Notation "x <- y ; z" := (bind y (fun x : _ => z)) (at level 30, right associativity).
Notation "++ k ; c" := (inc k c) (at level 30, right associativity).
*)

Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Arith Arith.Even Arith.Div2.
Require Import Omega.
Require Import Program.Syntax.
Require Import braun util.
Require Import log.

Program Fixpoint insert0 {A:Set} (x:A) (b:@bin_tree A)
: @C _ (fun (b':@bin_tree A) (cost:nat) =>
          forall n,
            Braun b n ->
            Braun b' (S n) ->
            cost = fl_log n + 1) :=
  match b with
    | bt_mt =>
      (inc _ 1
           (ret _ (bt_node x bt_mt bt_mt) _))
    | bt_node y s t =>
      (bind0 (insert0 y t)
            (fun st =>
               (inc _ 1
                    (ret _ (bt_node x st s) _)))
            _)
  end.
Obligations.

(* Obligation 2 is clearly false. *)

Admit Obligations.

(* XXX This next one requires a great leap to figure out what the
connection is *)

Program Fixpoint insert1 {A:Set} (x:A) (b:@bin_tree A)
: @C _ (fun (b':@bin_tree A) (cost:nat) =>
          forall n,
            Braun b n ->
            Braun b' (S n) ->
            cost = fl_log n + 1) :=
  match b with
    | bt_mt =>
      (inc _ 1
           (ret _ (bt_node x bt_mt bt_mt) _))
    | bt_node y s t =>
      (bind1 _ (insert1 y t)
            (fun st =>
               (inc _ 1
                    (ret _ (bt_node x st s) _)))
            _)
  end.



Next Obligation.
  rename H into Bb.
  rename H0 into Bb'.
  invclr Bb. auto.
Qed.

Next Obligation.
  rename H into Bb.
  rename H0 into Bb'.
  invclr Bb.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.
  invclr Bb'.
  rename H3 into BP'.
  rename H4 into Bt'.
  rename H5 into Bs'.
  rename H2 into EQ.
  replace t_size0 with s_size in *. (* same_structure *)
  replace s_size0 with (t_size +1) in *; try omega.
  



      (@inc _ _ _ 1 (@ret _ _ (bt_node x bt_mt bt_mt)))
  end.


    | bt_node y s t =>
      (st <- (insert 0 y t);
       ++1 ;
       ret (bt_node x t s))
  end.


{ b' : @bin_tree A | 
    forall cost n,
      Braun b n ->
      Braun b' (S n) ->
      cost = fl_log n + 1 } :=
  _.


: @C (@bin_tree A) _ (fun n b' => forall n', Braun b n' -> Braun b (S n') -> n = fl_log n' + 1)  :=
