Require Import braun Omega.
Require Import Arith.Even Arith.Div2 Arith List.
Set Implicit Arguments.

Program Definition helper_ss_st A (x:A) (m:nat) (pr : braun_tree A (m+1) * braun_tree A m)
: (braun_tree A (2*m+3) * braun_tree A (2*m+2)) :=
  match pr with
    | (s,t) => (Node x (m+1) (m+1) _ s s, Node x (m+1) m _ s t)
  end.

Obligation 1. omega. Qed.
Obligation 2. omega. Qed.
Obligation 3. omega. Qed.
Obligation 4. omega. Qed.

Program Definition helper_st_tt A (x:A) (m:nat) (pr : braun_tree A (m+1) * braun_tree A m)
: (braun_tree A (2*m+2) * braun_tree A (2*m+1)) :=
  match pr with
    | (s,t) => (Node x (m+1) m _ s t, Node x m m _ t t)
  end.

Obligation 1. omega. Qed.
Obligation 2. omega. Qed.
Obligation 3. omega. Qed.

Program Fixpoint copy2 A (x:A) n : braun_tree A (n+1) * braun_tree A n :=
  Fix lt_wf
      (fun n => braun_tree A (n+1) * braun_tree A n)%type
      (fun n copy2 => 
         match n with 
           | 0 => (Node x 0 0 _ Empty Empty, Empty)
           | S n' => 
             match even_odd_dec n' with
               | right H =>
                 helper_ss_st x (copy2 (proj1_sig (odd_S2n n' H)) _)
               | left H => 
                 helper_st_tt x (copy2 (proj1_sig (even_2n n' H)) _)
             end
         end) n.

Lemma lt_div2' : forall n, div2 n < S n.
 intros n.
 apply (le_lt_trans (div2 n) (div2 (S n)) (S n)).
 apply (ind_0_1_SS (fun n => div2 n <= div2 (S n))).
  constructor.
  constructor; reflexivity.
  intros; simpl; apply (plus_le_compat_l (div2 n0) (div2 (S n0)) 1); assumption.

 apply lt_div2; induction n; constructor; try assumption.
Qed.

Lemma zero_left : forall n, n+0=n. intros n. omega. Qed.
Lemma zero_left_minus : forall n, n-0=n. intros n. omega. Qed.

Obligation 2. apply lt_div2'. Qed.
Obligation 5. apply lt_div2'. Qed.

Obligation 3.
  clear Heq_anonymous.
  apply odd_double in H.
  rewrite zero_left.
  rewrite plus_comm.
  rewrite (plus_comm n' 1).
  simpl.
  unfold double in H.
  rewrite <- H.
  reflexivity.
Qed.

Obligation 4.
  clear Heq_anonymous.
  apply odd_double in H.
  rewrite zero_left.
  rewrite plus_comm.
  simpl.
  unfold double in H.
  rewrite <- H.
  reflexivity.
Qed.

Obligation 6.
  clear Heq_anonymous.
  apply even_double in H.
  rewrite zero_left.
  rewrite plus_comm.
  rewrite (plus_comm n' 1).
  simpl.
  unfold double in H.
  rewrite <- H.
  reflexivity.
Qed.

Obligation 7.
  clear Heq_anonymous.
  apply even_double in H.
  rewrite zero_left.
  rewrite plus_comm.
  simpl.
  unfold double in H.
  rewrite <- H.
  reflexivity.
Qed.

Definition copy A (x:A) n : braun_tree A n :=
  match copy2 x n with
    | (a,b) => b
  end.
