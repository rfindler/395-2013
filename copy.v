Require Import braun util.
Require Import Arith.Even Arith.Div2 Omega.
Set Implicit Arguments.

Program Definition copy2 A (x:A) : forall n, braun_tree A (n+1) * braun_tree A n :=
  Fix lt_wf _
      (fun n copy2 =>
         match n with
           | 0 => (Node x 0 0 _ Empty Empty, Empty)
           | S n' => 
             match even_odd_dec n' with
               (* odd *)
               | right H =>
                 let m := odd_S2n n' H
                 in let (s, t) := copy2 (proj1_sig m) _
                    in (Node x (m+1) (m+1) _ s s, Node x (m+1) m _ s t)
               (* even *)
               | left H =>
                 let m := even_2n n' H 
                 in let (s, t) := copy2 (proj1_sig m) _
                    in (Node x (m+1) m _ s t, Node x m m _ t t)
             end
         end).

Lemma odd_cleanup_1 : 
  forall n, 
    odd n -> div2 n + 1 + (div2 n + 1) + 1 = S (n + 1).
  intros n H.
  apply odd_double in H.
  unfold double in H.
  omega.
Qed.

Lemma odd_cleanup_2 :
  forall n,
    odd n -> div2 n + 1 + div2 n + 1 = S n.
  intros n H.
  apply odd_double in H.
  unfold double in H.
  omega.
Qed.

Lemma even_cleanup_1 : 
  forall n,
    even n -> div2 n + 1 + div2 n + 1 = S (n + 1).
  intros n H.
  apply even_double in H.
  unfold double in H.
  omega.
Qed.

Lemma even_cleanup_2 :
  forall n,
    even n -> div2 n + div2 n + 1 = S n.
  intros n H.
  apply even_double in H.
  unfold double in H.
  omega.
Qed.

Solve Obligations using (intros; omega).
Obligation 4. rewrite odd_cleanup_1. omega. assumption. Qed.
Obligation 6. rewrite odd_cleanup_2. omega. assumption. Qed.
Obligation 9. rewrite even_cleanup_1. omega. assumption. Qed.
Obligation 11. rewrite even_cleanup_2. omega. assumption. Qed.

Definition copy A (x:A) n := snd (copy2 x n).
