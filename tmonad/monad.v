(* START: C *)
Definition TC (M:Set -> Set) (A:Set) (P:M A -> nat -> Prop) : Set :=
   {a : M A | exists (an:nat), (P a an)}.
(* STOP: C *)
Hint Unfold TC.

Definition C := TC (fun x => x).
Hint Unfold C.

(* START: ret *)
Definition Tret (M:Set -> Set) 
                (A:Set)
                (ret : A -> M A)
                (P:M A -> nat -> Prop)
                (a:A) 
                (Pa0:P (ret a) 0) : TC M A P.
(* STOP: ret *)
Proof.
  exists (ret a).
  exists 0.
  apply Pa0.
Defined.

Definition ret A := Tret (fun x => x) A (fun x => x).

(* START: bind *)
Definition Tbind 
           (M:Set -> Set)
           (A:Set) (PA:M A -> nat -> Prop)
           (B:Set) (PB:M B -> nat -> Prop)
           (bind : M A -> (A -> M B) -> M B)
           (am:TC M A PA) 
           (bf:forall (a:M A)
                      (pa:exists an, PA a an),
                 TC M B 
                    (fun b bn => 
                       forall an, 
                         PA a an ->
                         PB b (an+bn)))
: TC M B PB.
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

Definition bind A PA B PB := Tbind (fun x => x) A PA B PB (fun x f => f x).

(* START: inc *)
Definition Tinc (M: Set -> Set) (A:Set) 
           k
           (PA : M A -> nat -> Prop)
           (x:TC M A (fun x xn =>
                        forall xm, 
                          xn + k = xm ->
                          PA x xm))
: TC M A PA.
(* STOP: inc *)
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + k).
  apply Px.
  reflexivity.
Defined.

Definition inc := Tinc (fun x => x).

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "+= k ; c" := (inc _ k _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ _ y (fun (x : _) (am : _) => z) )
                           (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ _ x y) (at level 55).
Notation "x >> y" := (bind _ _ _ _ x (fun _ => y)) (at level 30, right associativity).

Notation "{! x !:! A !<! c !>!  P !}" := (C A (fun (x:A) (c:nat) => P)) (at level 55).
