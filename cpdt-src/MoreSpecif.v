(* Copyright (c) 2008, 2011, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* Types and notations presented in Chapter 6 *)

Set Implicit Arguments.


Notation "!" := (False_rec _ _) : specif_scope.
Notation "[ e ]" := (exist _ e _) : specif_scope.
Notation "x <== e1 ; e2" := (let (x, _) := e1 in e2)
(right associativity, at level 60) : specif_scope.

Local Open Scope specif_scope.
Delimit Scope specif_scope with specif.

Notation "'Yes'" := (left _ _) : specif_scope.
Notation "'No'" := (right _ _) : specif_scope.
Notation "'Reduce' x" := (if x then Yes else No) (at level 50) : specif_scope.

Notation "x || y" := (if x then Yes else Reduce y) (at level 50, left associativity) : specif_scope.

Section sumbool_and.
  Variables P1 Q1 P2 Q2 : Prop.

  Variable x1 : {P1} + {Q1}.
  Variable x2 : {P2} + {Q2}.

  Definition sumbool_and : {P1 /\ P2} + {Q1 \/ Q2} :=
    match x1 with
      | left HP1 =>
        match x2 with
          | left HP2 => left _ (conj HP1 HP2)
          | right HQ2 => right _ (or_intror _ HQ2)
        end
      | right HQ1 => right _ (or_introl _ HQ1)
    end.
End sumbool_and.

Infix "&&" := sumbool_and (at level 40, left associativity) : specif_scope.

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

Notation "{{ x | P }}" := (maybe (fun x => P)) : specif_scope.
Notation "??" := (Unknown _) : specif_scope.
Notation "[| x |]" := (Found _ x _) : specif_scope.

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60) : specif_scope.

Notation "!!" := (inright _ _) : specif_scope.
Notation "[|| x ||]" := (inleft _ [x]) : specif_scope.

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60) : specif_scope.

Notation "e1 ;; e2" := (if e1 then e2 else ??)
  (right associativity, at level 60) : specif_scope.

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
  (right associativity, at level 60) : specif_scope.


Section partial.
  Variable P : Prop.

  Inductive partial : Set :=
  | Proved : P -> partial
  | Uncertain : partial.
End partial.

Notation "[ P ]" := (partial P) : type_scope.

Notation "'Yes'" := (Proved _) : partial_scope.
Notation "'No'" := (Uncertain _) : partial_scope.

Local Open Scope partial_scope.
Delimit Scope partial_scope with partial.

Notation "'Reduce' v" := (if v then Yes else No) : partial_scope.
Notation "x || y" := (if x then Yes else Reduce y) : partial_scope.
Notation "x && y" := (if x then Reduce y else No) : partial_scope.
