(* Read chapters 1 and 2 of CPDT. 

   Set up Coq on your machine, following the instructions in the book.

   Then add PAIRS to this file, everywhere appropriate.

   A pair has three operations: build a pair from two other values,
   extract the first component of the pair, and extract the second
   component. Start by adding these operations to 'exp' and then 
   see how far you get.
 *)

Require Import Bool Arith List CpdtTactics.
Set Implicit Arguments.

(** * Arithmetic Expressions Over Natural Numbers *)

(* Source language *)

Inductive unop : Set := Fst | Snd.
Inductive binop : Set := Plus | Times | Pair.

Inductive exp : Set :=
| Const : nat -> exp
| Unop  : unop -> exp -> exp
| Binop : binop -> exp -> exp -> exp.

Inductive val : Set :=
| VNat : nat -> val
| VPair : val -> val -> val.

Definition mathyDenote (f : nat -> nat -> nat) : val -> val -> option val :=
  fun v1 v2 =>
    match v1 with
      | VNat n1 =>
        match v2 with
          | VNat n2 => Some (VNat (f n1 n2))
          | _ => None
        end
      | _ => None
    end.
  

Definition binopDenote (b : binop) : val -> val -> option val :=
  match b with
    | Pair => fun v1 v2 => Some (VPair v1 v2)
    | Plus => mathyDenote plus
    | Times => mathyDenote mult
  end.

Definition unopDenote (u : unop) : val -> option val :=
  fun v =>
    match v with
      | VPair v1 v2 =>
        match u with
          | Fst => Some v1
          | Snd => Some v2
        end
      | _ => None
    end.

Fixpoint expDenote (e : exp) : option val :=
  match e with
    | Const n => Some (VNat n)
    | Binop b e1 e2 =>
      match (expDenote e2) with
        | Some v2 =>
          match (expDenote e1) with
            | Some v1 =>
              (binopDenote b) v1 v2
            | None => None
          end
        | None => None
      end
    | Unop u e =>
      match (expDenote e) with
        | Some v =>
          (unopDenote u) v
        | None => None
      end
  end.

Eval simpl in expDenote (Const 42).

Eval simpl in expDenote (Binop Plus (Const 2) (Const 2)).

Eval simpl in expDenote (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Eval simpl in expDenote (Binop Pair (Const 2) (Const 7)).
Eval simpl in expDenote (Unop Fst (Binop Pair (Const 2) (Const 7))).
Eval simpl in expDenote (Unop Snd (Binop Pair (Const 2) (Const 7))).
Eval simpl in expDenote (Unop Snd (Const 2)).
Eval simpl in expDenote (Binop Plus
                               (Binop Pair (Const 2) (Const 7))
                               (Const 3)).

(* Target language *)

Inductive instr : Set :=
| iConst : nat -> instr
| iUnop  : unop -> instr
| iBinop : binop -> instr.

Definition prog := list instr.
Definition stack := list val.

Definition bind {A B} (o : option A) (f : A -> option B) : option B :=
  match o with
    | Some x => f x
    | None => None
  end.

Definition instrDenote (i : instr) (s : stack) : option stack :=
  match i with
    | iConst n => Some (VNat n :: s)
    | iBinop b =>
      match s with
        | arg1 :: arg2 :: s' =>
          bind ((binopDenote b) arg1 arg2)
               (fun v => Some (v :: s'))
        | _ => None
      end
    | iUnop u =>
      match s with
        | arg :: s' => match (unopDenote u arg) with
                         | Some v => Some (v :: s')
                         | None => None
                       end
        | _ => None
      end
  end.

Fixpoint progDenote (p : prog) (s : stack) : option stack :=
  match p with
    | nil => Some s
    | i :: p' =>
      match instrDenote i s with
        | None => None
        | Some s' => progDenote p' s'
      end
  end.

(* Compilation *)

Fixpoint compile (e : exp) : prog :=
  match e with
    | Const n => iConst n :: nil
    | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    | Unop u e => compile e ++ iUnop u :: nil
  end.

Eval simpl in compile (Const 42).

Eval simpl in compile (Binop Plus (Const 2) (Const 2)).

Eval simpl in compile (Binop Times (Binop Plus (Const 2) (Const 2)) (Const 7)).

Eval simpl in compile (Unop Snd (Binop Pair (Const 2) (Const 7))).
Eval simpl in compile (Unop Snd (Const 2)).
Eval simpl in compile (Binop Plus
                               (Binop Pair (Const 2) (Const 7))
                               (Const 3)).

Eval simpl in progDenote (compile (Const 42)) nil.

Eval simpl in progDenote (compile (Binop Plus (Const 2) (Const 2))) nil.

Eval simpl in progDenote (compile (Binop Times (Binop Plus (Const 2) (Const 2))
                                         (Const 7))) nil.

Eval simpl in progDenote (compile  (Unop Snd (Binop Pair (Const 2) (Const 7)))) nil.
Eval simpl in progDenote (compile  (Unop Snd (Const 2))) nil.
Eval simpl in progDenote (compile  (Binop Plus
                                          (Binop Pair (Const 2) (Const 7))
                                          (Const 3))) nil.


Lemma compile_correct' : forall e s p, progDenote (compile e ++ p) s =
                                       bind (expDenote e)
                                            (fun v =>
                                               progDenote p (v :: s)).
  induction e; crush.
  induction (expDenote e); crush.
  induction (unopDenote u a); crush.

  induction (expDenote e2); crush.
  induction (expDenote e1); crush.
  induction (binopDenote b a0 a); crush.
Qed.

Theorem compile_correct : forall e, 
                            progDenote (compile e) nil = bind (expDenote e)
                                                              (fun v => Some (v :: nil)).
  intros.
  rewrite (app_nil_end (compile e)).
  rewrite compile_correct'.
  reflexivity.
Qed.


(** * Typed Expressions *)

Inductive type : Set :=
| Nat
| Bool
| Prod : type -> type -> type.

Inductive tbinop : type -> type -> type -> Set :=
| TPlus : tbinop Nat Nat Nat
| TTimes : tbinop Nat Nat Nat
| TEq : forall t, tbinop t t Bool
| TLt : tbinop Nat Nat Bool
| TPair : forall t1 t2, tbinop t1 t2 (Prod t1 t2).

Inductive tunop : type -> type -> Set :=
| TFst : forall t1 t2, tunop (Prod t1 t2) t1
| TSnd : forall t1 t2, tunop (Prod t1 t2) t2.

Inductive texp : type -> Set :=
| TNConst : nat -> texp Nat
| TBConst : bool -> texp Bool
| TUnop  : forall t1 t2, tunop t1 t2 -> texp t1 -> texp t2
| TBinop : forall t1 t2 t, tbinop t1 t2 t -> texp t1 -> texp t2 -> texp t.

Fixpoint typeDenote (t : type) : Set :=
  match t with
    | Nat => nat
    | Bool => bool
    | Prod t1 t2 => prod (typeDenote t1) (typeDenote t2)
  end.

Fixpoint tEqDenote (t : type) : typeDenote t -> typeDenote t -> bool :=
  match t with
    | Nat => beq_nat
    | Bool => eqb
    | Prod t1 t2 =>
      fun p1 p2 =>
        andb ((tEqDenote t1) (fst p1) (fst p2))
             ((tEqDenote t2) (snd p1) (snd p2))
  end.

Definition tunopDenote arg res (u : tunop arg res) : typeDenote arg -> typeDenote res :=
  match u in tunop arg res return typeDenote arg -> typeDenote res with
    | TFst _ _ => fun (p : prod _ _ ) => fst p
    | TSnd _ _ => fun (p : prod _ _ ) => snd p
  end.

Definition tbinopDenote arg1 arg2 res (b : tbinop arg1 arg2 res)
  : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b in tbinop arg1 arg2 res return typeDenote arg1 -> typeDenote arg2 -> typeDenote res with
    | TPlus => plus
    | TTimes => mult
    | TEq t => tEqDenote t
    | TLt => leb
    | TPair t1 t2 => pair 
  end.

Fixpoint texpDenote t (e : texp t) : typeDenote t :=
  match e with
    | TNConst n => n : typeDenote Nat
    | TBConst b => b
    | TUnop _ _ u e => (tunopDenote u) (texpDenote e)
    | TBinop _ _ _ b e1 e2 => (tbinopDenote b) (texpDenote e1) (texpDenote e2)
  end.

Eval simpl in texpDenote (TNConst 42).

Eval simpl in texpDenote (TBConst true).

Eval simpl in texpDenote (TBinop TTimes (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).

Eval simpl in texpDenote (TBinop (TEq Nat) (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).

Eval simpl in texpDenote (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)).

Definition tstack := list type.

Inductive tinstr : tstack -> tstack -> Set :=
| TiNConst : forall s, nat -> tinstr s (Nat :: s)
| TiBConst : forall s, bool -> tinstr s (Bool :: s)
| TiUnop  : forall arg res s, tunop arg res -> tinstr (arg :: s) (res :: s)
| TiBinop : forall arg1 arg2 res s,
  tbinop arg1 arg2 res
  -> tinstr (arg1 :: arg2 :: s) (res :: s).

Inductive tprog : tstack -> tstack -> Set :=
| TNil : forall s, tprog s s
| TCons : forall s1 s2 s3,
  tinstr s1 s2
  -> tprog s2 s3
  -> tprog s1 s3.

Fixpoint vstack (ts : tstack) : Set :=
  match ts with
    | nil => unit
    | t :: ts' => typeDenote t * vstack ts'
  end%type.

Definition tinstrDenote ts ts' (i : tinstr ts ts') : vstack ts -> vstack ts' :=
  match i in tinstr ts ts' return vstack ts -> vstack ts' with
    | TiNConst _ n => fun s => (n, s)
    | TiBConst _ b => fun s => (b, s)
    | TiUnop _ _ _ u =>
      fun s =>
        let '(arg, s') := s in
        ((tunopDenote u) arg, s')
    | TiBinop _ _ _ _ b => fun s =>
      let '(arg1, (arg2, s')) := s in
        ((tbinopDenote b) arg1 arg2, s')
  end.

Fixpoint tprogDenote ts ts' (p : tprog ts ts') : vstack ts -> vstack ts' :=
  match p with
    | TNil _ => fun s => s
    | TCons _ _ _ i p' => fun s => tprogDenote p' (tinstrDenote i s)
  end.

Fixpoint tconcat ts ts' ts'' (p : tprog ts ts') : tprog ts' ts'' -> tprog ts ts'' :=
  match p with
    | TNil _ => fun p' => p'
    | TCons _ _ _ i p1 => fun p' => TCons i (tconcat p1 p')
  end.

Fixpoint tcompile t (e : texp t) (ts : tstack) : tprog ts (t :: ts) :=
  match e with
    | TNConst n => TCons (TiNConst _ n) (TNil _)
    | TBConst b => TCons (TiBConst _ b) (TNil _)
    | TUnop _ _ u e => tconcat (tcompile e _) (TCons (TiUnop _ u) (TNil _))
    | TBinop _ _ _ b e1 e2 => tconcat (tcompile e2 _)
      (tconcat (tcompile e1 _) (TCons (TiBinop _ b) (TNil _)))
  end.
Print  tcompile.
Eval simpl in tprogDenote (tcompile (TNConst 42) nil) tt.

Eval simpl in tprogDenote (tcompile (TBConst true) nil) tt.

Eval simpl in tprogDenote (tcompile (TBinop TTimes (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.

Eval simpl in tprogDenote (tcompile (TBinop (TEq Nat) (TBinop TPlus (TNConst 2)
  (TNConst 2)) (TNConst 7)) nil) tt.

Eval simpl in tprogDenote (tcompile (TBinop TLt (TBinop TPlus (TNConst 2) (TNConst 2))
  (TNConst 7)) nil) tt.

Lemma tconcat_correct : forall ts ts' ts'' (p : tprog ts ts') (p' : tprog ts' ts'')
  (s : vstack ts),
  tprogDenote (tconcat p p') s
  = tprogDenote p' (tprogDenote p s).
  induction p; crush.
Qed.

Hint Rewrite tconcat_correct.

Lemma tcompile_correct' : forall t (e : texp t) ts (s : vstack ts),
  tprogDenote (tcompile e ts) s = (texpDenote e, s).
  induction e; crush.
Qed.

Hint Rewrite tcompile_correct'.

Theorem tcompile_correct : forall t (e : texp t),
  tprogDenote (tcompile e nil) tt = (texpDenote e, tt).
  crush.
Qed.
