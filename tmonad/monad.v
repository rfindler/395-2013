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

Lemma Tbind_quasiresonable:
forall (M:Set -> Set)
(bind : forall (A B:Set) (W: M B -> Prop),
             M A ->
             (A -> {mb : (M B) | W mb}) -> 
             {mb : (M B) | W mb}),
(forall (A B:Set),
             M A ->
             (A -> M B) -> (M B)).
Proof.
  intros M bind.
  intros A B ma f.
  
  edestruct (bind A B (fun _ => True) ma).
  intros a. apply f in a.
  exists a. auto.

  apply x.
Qed.

(* START: bind *)
Definition Tbind 

           (M:Set -> Set)
           (bind : forall (A B:Set) (W: M B -> Prop),
             M A ->
             (A -> {mb : (M B) | W mb}) -> 
             {mb : (M B) | W mb})
           
           (A:Set) (PA:M A -> nat -> Prop)
           (B:Set) (PB:M B -> nat -> Prop)
           (am:TC M A PA) 
           (bf:forall (a:A)
                      (pa:exists an, PA (proj1_sig am) an),
                 TC M B 
                    (fun b bn => 
                       forall an, 
                         PA (proj1_sig am) an ->
                         PB b (an+bn)))
: TC M B PB.
(* STOP: bind *)
Proof.
  destruct am as [ma Pma].
  simpl in bf.

  refine 
    (_ (bind A B
      (fun mb => exists an : nat, forall an0 : nat, PA ma an0 -> PB mb (an0 + an)) ma _)).

  intros [mb Pmb].
  exists mb.
  destruct Pma as [an Pma].
  destruct Pmb as [bn Pmb].
  exists (an + bn).
  eapply Pmb.
  apply Pma.

  intros a.
  edestruct (bf a Pma) as [mb Pmb].
  exists mb.
  apply Pmb.
Defined.

Definition bind A PA B PB := Tbind (fun x => x) (fun A B W x f => f x) A PA B PB.

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
