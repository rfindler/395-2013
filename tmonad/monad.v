Definition C (A:Set) (P:A -> nat -> Prop) : Set := {a | exists n, (P a n)}.
Hint Unfold C.

Definition ret (A:Set) (PA:A -> nat -> Prop) (x:A) (PAx:PA x 0) : C A PA.
Proof.
  exists x.
  exists 0.
  apply PAx.
Defined.

Definition bind (A:Set) (B:Set)
           (PA:A -> nat -> Prop) (PAB:A -> B -> nat -> Prop)
           (xm:C A PA) 
           (yf:forall (x:A),
                 C B 
                   (fun y yn => 
                      forall xn, 
                        PA x xn ->
                        PAB x y (xn+yn)))
: C B (PAB (proj1_sig xm)).
Proof.
  destruct xm as [x Px].
  edestruct (yf x) as [y Py].
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply Py.
  apply Px.
Defined.

Definition inc (A:Set) PA (x:C A (fun x xn => PA x (xn+1)))
: C A PA.
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + 1).
  apply Px.
Defined.

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "++ ; c" := (inc _ _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ (fun _ => _) y (fun x : _ => z) ) (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ (fun _ => _) x y) (at level 55).
Notation "x >> y" := (bind _ _ _ (fun _ => _) x (fun _ => y)) (at level 30, right associativity).

Notation "{ x !:! A !<! c !>!  P  }" := (C A (fun (x:A) (c:nat) => P)) (at level 55).
