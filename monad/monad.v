(* START: C *)
Definition C (A:Set) (P:A -> nat -> Prop) : Set :=
   {a : A | exists (an:nat), (P a an)}.
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

(* START: bind *)
Definition bind (A:Set) (PA:A -> nat -> Prop)
                (B:Set) (PB:B -> nat -> Prop)
                (am:C A PA) 
                (bf:forall (a:A) (pa:exists an, PA a an),
                  C B (fun b bn => forall an, PA a an -> PB b (an+bn)))
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
Definition inc (A:Set) k (PA : A -> nat -> Prop)
           (xc:C A (fun x xn => forall xm, xn + k = xm -> PA x xm))
: C A PA.
(* STOP: inc *)
Proof.
  destruct xc as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + k).
  apply Px.
  reflexivity.
Defined.

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "+= k ; c" := (inc _ k _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ _ y (fun (x : _) (am : _) => z) )
                           (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ _ x y) (at level 55).
Notation "x >> y" := (bind _ _ _ _ x (fun _ => y)) (at level 30, right associativity).

Notation "{! x !:! A !<! c !>!  P !}" := (C A (fun (x:A) (c:nat) => P)) (at level 55).

