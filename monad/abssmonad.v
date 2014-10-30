Require Import Program.

(* 
   Start with Indexed State Monad 
   The indices S1, S2 allow us to change the type of the state.
*)
Definition IState (S1 S2 A : Set) : Set := (S1 -> (S2 * A)).
Definition State S := IState S S.
Definition isret (S A : Set) (x : A) : State S A :=
  fun s => (s, x).

Definition isbnd (S1 S2 S3 A B : Set) (m : IState S1 S2 A) (f : A -> IState S2 S3 B) : IState S1 S3 B :=
  fun s1 : S1 =>
    let (s2, x) := m s1 in f x s2.

(* Now add count and prop on top of that *)
Definition ISC (S1 S2 A : Set) (P : S1 -> S2 -> A -> nat -> Prop) : Set :=
  forall s1 : S1, { (x, s2) : A * S2 | exists n, P s1 s2 x n }.
Definition SC S := ISC S S.

Hint Unfold ISC.
Hint Unfold SC.

Definition ret (S A : Set) (x : A) : SC S A (fun _ _ x' n => x = x' /\ n = 0).
  unfold SC.
  unfold ISC.
  intros st.
  exists (x, st).
  exists 0.
  auto.
Defined.

Definition bind
           (S1 S2 S3 A B : Set)
           (PA : S1 -> S2 -> A -> nat -> Prop)
           (PB : A -> S2 -> S3 -> B -> nat -> Prop)
           (m : ISC S1 S2 A PA)
           (f : forall (x : A), ISC S2 S3 B (PB x))
: ISC S1 S3 B (fun s1 s3 b bn =>
                 exists a an s2, PA s1 s2 a an /\ PB a s2 s3 b bn).
Proof.
  unfold ISC.
  intros.
  unfold ISC in *.
  destruct (m s1) as [ [a s2] PfA].
  destruct (f a s2) as [[b s3] PfB].
  exists (b, s3).
  destruct PfA as [an PfA].
  destruct PfB as [bn PfB].
  exists bn a an s2.
  auto.
Defined.
