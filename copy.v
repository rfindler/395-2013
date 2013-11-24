Require Import braun Omega.
Require Import Arith.Even Arith.Div2.
Set Implicit Arguments.

Program Definition helper_ss_st A (x:A) (m:nat) 
        (pr : braun_tree A (m+1) * braun_tree A m)
: (braun_tree A (2*m+3) * braun_tree A (2*m+2)) :=
  match pr with
    | (s,t) => (Node x (m+1) (m+1) _ s s, Node x (m+1) m _ s t)
  end.

Solve Obligations using (intros; omega).

Program Definition helper_st_tt A (x:A) (m:nat) 
        (pr : braun_tree A (m+1) * braun_tree A m)
: (braun_tree A (2*m+2) * braun_tree A (2*m+1)) :=
  match pr with
    | (s,t) => (Node x (m+1) m _ s t, Node x m m _ t t)
  end.

Solve Obligations using (intros; omega).

Lemma div2_monotone : forall n, (div2 n <= div2 (S n)).
  apply (ind_0_1_SS (fun n => div2 n <= div2 (S n))); 
  [ | | intros n IndHyp; simpl in IndHyp]; 
  simpl; omega.
Qed.

Lemma lt_div2' : forall n, div2 n < S n.
 intros n.

 apply (le_lt_trans (div2 n) (div2 (S n)) (S n));
   [ apply div2_monotone |  apply lt_div2 ] ;
   omega.
Qed.

Hint Resolve lt_div2'.

Program Definition copy2 A (x:A) : forall n, braun_tree A (n+1) * braun_tree A n :=
  Fix lt_wf _
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
         end).

Lemma odd_cleanup : 
  forall n k, 
    odd n -> div2 n + (div2 n + 0) + (k + 1) = n + k.
  intros n k H.
  apply odd_double in H.
  unfold double in H.
  omega.
Qed.

Lemma even_cleanup : 
  forall n k,
    even n -> div2 n + (div2 n + 0) + k = n + k.
  intros n k H.
  apply even_double in H.
  unfold double in H.
  omega.
Qed.

Obligation 3. rewrite (odd_cleanup 2). omega. assumption. Qed.
Obligation 4. rewrite (odd_cleanup 1). omega. assumption. Qed.

Obligation 6. rewrite (even_cleanup 2). omega. assumption. Qed.
Obligation 7. rewrite (even_cleanup 1). omega. assumption. Qed.

Definition copy A (x:A) n := snd (copy2 x n).
