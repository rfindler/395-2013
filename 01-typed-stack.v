(*
  A variation on the code in chaper 1 where 
  all types are reprsented as Nat and then
  a proof that both behave the same way.
*)

Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments. 

Inductive type : Set := Nat | Bool.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t
| TIf : forall t, texp Bool -> texp t -> texp t -> texp t.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
  end%type.

Fixpoint cmp (t : type) : (typeDenote t) -> (typeDenote t) ->  bool :=
  match t with 
    | Nat => beq_nat
    | Bool => eqb
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq t => cmp t
    | TLt => leb
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n
    | TBConst b => b
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
    | TIf _ tst thn els => 
      match (texpDenote tst) with
        | true => (texpDenote thn)
        | false => (texpDenote els)
      end
  end.

Eval simpl in texpDenote (TNConst 42).

Eval simpl in texpDenote (TBConst false).

Eval simpl in texpDenote (TBConst true).

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).

Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).

Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).


Definition typeDenote' (t : type) : Set := nat.

Definition tbinopDenote' arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote' arg1 -> typeDenote' arg2 -> typeDenote' res :=   
  match b with
    | TPlus => plus
    | TTimes => mult
    | TEq t => fun x => fun y =>  match (beq_nat x y) with | true => 1 | false => 0 end
    | TLt => fun x => fun y =>  match (leb x y) with | true => 1 | false => 0 end
  end%nat.

Fixpoint texpDenote' t (e : texp t) : typeDenote' t :=
  match e with
    | TNConst n => n
    | TBConst b => match b with | true => 1 | false => 0 end
    | TBinop _ _ _ b e1 e2 => (tbinopDenote' b)
                                (texpDenote' e1)
                                (texpDenote' e2)
    | TIf _ tst thn els => match (beq_nat (texpDenote' tst) 1) with
                               | true => (texpDenote' thn)
                               | false => (texpDenote' els)
                           end
  end.

Eval simpl in texpDenote' (TIf (TBConst true) (TNConst 3) (TNConst 4)).

Definition coerce (t : type) : typeDenote t -> typeDenote' t :=
  match t with
    | Nat => fun x => x
    | Bool => fun b => if b then 1 else 0
  end.

Lemma binop_coerce : 
  forall tres t1 t2 (b : tbinop t1 t2 tres)
         (v1 : typeDenote t1) (v2 : typeDenote t2),
     tbinopDenote' b (coerce t1 v1) (coerce t2 v2) =
     coerce tres (tbinopDenote b v1 v2).
  induction b; crush.
  induction t; crush.
  destruct v1; destruct v2; crush.
Qed.

Hint Rewrite binop_coerce.

Lemma if_coerce : 
  forall t
         (v1 : bool) 
         (v2 : typeDenote t)
         (v3 : typeDenote t),
   (if beq_nat (if v1 then 1 else 0) 1
    then coerce t v2
    else coerce t v3) =
   coerce t (if v1 then v2 else v3).
  destruct v1; crush.
Qed.

Hint Rewrite if_coerce.

Lemma sameDenote_coerce : 
  forall t (e : texp t),
    texpDenote' e = coerce _ (texpDenote e).
  induction e; crush.
Qed.

Theorem sameDenote : forall (e: texp Nat), 
                       texpDenote' e = texpDenote e.
  apply sameDenote_coerce.
Qed.
