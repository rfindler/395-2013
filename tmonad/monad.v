(* START: C *)
Definition C (A:Set) (P:A -> nat -> Prop) : Set := {a : A | exists (an:nat), (P a an)}.
(* STOP: C *)
Hint Unfold C.

(* START: ret *)
Definition ret (A:Set) (P:A -> nat -> Prop) (a:A) (Pa0:P a 0) : C A P.
(* STOP: ret *)
Proof.
  exists a.
  exists 0.
  apply Pa0.
Defined.

(* START: bind1 *)
Definition 
  bind1
  (A:Set) (PA:A -> nat -> Prop)
  (B:Set) (PB:B -> nat -> Prop)
  (am:C A PA) 
  (bf:A -> C B PB)
: C B PB.
(* STOP: bind1 *)
Abort.

(* START: bind2 *)
Definition
  bind2 
  (A:Set) (PA:A -> nat -> Prop)
  (B:Set) (PB:B -> nat -> Prop)
  (am:C A PA) 
  (bf:A -> 
      C B 
        (fun b bn => 
           forall an, 
             PB b (bn+an)))
: C B PB.
(* STOP: bind2 *)
Abort.

(* START: bind3 *)
Definition
  bind3 
  (A:Set) (PA:A -> nat -> Prop)
  (B:Set) (PB:B -> nat -> Prop)
  (am:C A PA) 
  (bf:forall (a:A), 
        C B 
          (fun b bn => 
             forall an,
               PA a an ->
               PB b (bn+an)))
: C B PB.
(* STOP: bind3 *)
Abort.

(* START: bind *)
Definition
  bind 
  (A:Set) (PA:A -> nat -> Prop)
  (B:Set) (PB:B -> nat -> Prop)
  (am:C A PA) 
  (bf:forall (a:A)
             (pa:exists an, PA a an),
        C B 
          (fun b bn => 
             forall an, 
               PA a an ->
               PB b (an+bn)))
: C B PB.
(* STOP: bind *)
Proof.
  destruct am as [a Pa].
  edestruct (bf a Pa) as [b Pb].
  exists b.
  destruct Pa as [an Pa].
  destruct Pb as [bn Pb].
  exists (an + bn).
  eapply Pb.
  apply Pa.
Defined.

(* START: inc *)
Definition inc (A:Set) (P:A -> nat -> Prop) (am:C A (fun a an => P a (an+1)))
: C A P.
(* STOP: inc *)
Proof.
  destruct am as [a Pa].
  exists a.
  destruct Pa as [n Pa].
  exists (n + 1).
  apply Pa.
Defined.

(* this seems like it could replace inc, except
   that various hypotheses in various places get
   different names. So I just make a second 'inc'
   here for now with the plan to fix the other places
   when this turns out to actually work for insert.
*)
Definition inc2 (A:Set) 
           k
           (PA : A -> nat -> Prop)
           (x:C A (fun x xn => forall xm, xn + k = xm -> PA x xm))
: C A PA.
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + k).
  apply Px.
  reflexivity.
Defined.

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "++ ; c" := (inc _ _ c) (at level 30, right associativity).
Notation "+= k ; c" := (inc2 _ k _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ _ y (fun (x : _) (am : _) => z) ) (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ _ x y) (at level 55).
Notation "x >> y" := (bind _ _ _ _ x (fun _ => y)) (at level 30, right associativity).

Notation "{! x !:! A !<! c !>!  P !}" := (C A (fun (x:A) (c:nat) => P)) (at level 55).

