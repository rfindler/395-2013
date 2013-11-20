(* Copyright (c) 2008-2009, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Dependent list types presented in Chapter 9 *)

Require Import Arith List CpdtTactics.

Set Implicit Arguments.


Section ilist.
  Variable A : Type.

  Inductive ilist : nat -> Type :=
  | INil : ilist O
  | ICons : forall n, A -> ilist n -> ilist (S n).

  Definition hd n (ls : ilist (S n)) :=
    match ls in ilist n' return match n' with
                                  | O => unit
                                  | S _ => A
                                end with
      | INil => tt
      | ICons _ x _ => x
    end.
  Definition tl n (ls : ilist (S n)) :=
    match ls in ilist n' return match n' with
                                  | O => unit
                                  | S n => ilist n
                                end with
      | INil => tt
      | ICons _ _ ls' => ls'
    end.

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
      | INil => fun idx =>
        match idx in fin n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | ICons _ x ls' => fun idx =>
        match idx in fin n' return (fin (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.

  Section everywhere.
    Variable x : A.

    Fixpoint everywhere (n : nat) : ilist n :=
      match n with
        | O => INil
        | S n' => ICons x (everywhere n')
      end.
  End everywhere.

  Section singleton.
    Variables x default : A.

    Fixpoint singleton (n m : nat) : ilist n :=
      match n with
        | O => INil
        | S n' =>
          match m with
            | O => ICons x (everywhere default n')
            | S m' => ICons default (singleton n' m')
          end
      end.
  End singleton.

  Section map2.
    Variable f : A -> A -> A.

    Fixpoint map2 n (il1 : ilist n) : ilist n -> ilist n :=
      match il1 in ilist n return ilist n -> ilist n with
        | INil => fun _ => INil
        | ICons _ x il1' => fun il2 => ICons (f x (hd il2)) (map2 il1' (tl il2))
      end.
  End map2.

  Section fold.
    Variable B : Type.
    Variable f : A -> B -> B.
    Variable i : B.

    Fixpoint foldr n (il : ilist n) : B :=
      match il with
        | INil => i
        | ICons _ x il' => f x (foldr il')
      end.
  End fold.
End ilist.

Implicit Arguments INil [A].
Implicit Arguments First [n].

Section imap.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint imap n (il : ilist A n) : ilist B n :=
    match il with
      | INil => INil
      | ICons _ x il' => ICons (f x) (imap il')
    end.
End imap.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (x : A) (ls : list A), B x -> hlist ls -> hlist (x :: ls).

  Definition hhd ls (hl : hlist ls) :=
    match hl in hlist ls return match ls with
                                  | nil => unit
                                  | x :: _ => B x
                                end with
      | HNil => tt
      | HCons _ _ v _ => v
    end.

  Definition htl ls (hl : hlist ls) :=
    match hl in hlist ls return match ls with
                                  | nil => unit
                                  | _ :: ls' => hlist ls'
                                end with
      | HNil => tt
      | HCons _ _ _ hl' => hl'
    end.

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall ls, member (elm :: ls)
  | HNext : forall x ls, member ls -> member (x :: ls).

  Fixpoint hget ls (mls : hlist ls) : member ls -> B elm :=
    match mls with
      | HNil => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => B elm
                                          | _ :: _ => unit
                                        end) with
          | HFirst _ => tt
          | HNext _ _ _ => tt
        end
      | HCons _ _ x mls' => fun mem =>
        match mem in member ls' return (match ls' with
                                          | nil => Empty_set
                                          | x' :: ls'' =>
                                            B x' -> (member ls'' -> B elm) -> B elm
                                        end) with
          | HFirst _ => fun x _ => x
          | HNext _ _ mem' => fun _ get_mls' => get_mls' mem'
        end x (hget mls')
    end.

  Fixpoint happ (ls1 : list A) (hl1 : hlist ls1) : forall ls2, hlist ls2 -> hlist (ls1 ++ ls2) :=
    match hl1 in hlist ls1 return forall ls2, hlist ls2 -> hlist (ls1 ++ ls2) with
      | HNil => fun _ hl2 => hl2
      | HCons _ _ x hl1' => fun _ hl2 => HCons x (happ hl1' hl2)
    end.

  Variable f : forall x, B x.

  Fixpoint hmake (ls : list A) : hlist ls :=
    match ls with
      | nil => HNil
      | x :: ls' => HCons (f x) (hmake ls')
    end.

  Theorem hget_hmake : forall ls (m : member ls),
    hget (hmake ls) m = f elm.
    induction ls; crush;
      match goal with
        | [ |- context[match ?E with HFirst _ => _ | HNext _ _ _ => _ end] ] => dep_destruct E
      end; crush.
  Qed.
End hlist.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x ls].
Implicit Arguments hmake [A B].

Implicit Arguments HFirst [A elm ls].
Implicit Arguments HNext [A elm x ls].

Infix ":::" := HCons (right associativity, at level 60).
Infix "+++" := happ (right associativity, at level 60).

Section hmap.
  Variable A : Type.
  Variables B1 B2 : A -> Type.

  Variable f : forall x, B1 x -> B2 x.

  Fixpoint hmap (ls : list A) (hl : hlist B1 ls) : hlist B2 ls :=
    match hl with
      | HNil => HNil
      | HCons _ _ x hl' => f x ::: hmap hl'
    end.

  Theorem hmap_happ : forall ls2 (h2 : hlist B1 ls2) ls1 (h1 : hlist B1 ls1),
    hmap h1 +++ hmap h2 = hmap (h1 +++ h2).
    induction h1; crush.
  Qed.

  Theorem hget_hmap : forall elm ls (hls : hlist B1 ls) (m : member elm ls),
    hget (hmap hls) m = f (hget hls m).
    induction hls; crush;
      match goal with
        | [ |- context[match ?E with HFirst _ => _ | HNext _ _ _ => _ end] ] => dep_destruct E
      end; crush.
  Qed.
End hmap.

Implicit Arguments hmap [A B1 B2 ls].
