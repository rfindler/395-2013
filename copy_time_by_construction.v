Require Import braun util monad2 fl_log.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.

Set Implicit Arguments.

Section copy2.

  Variable A:Set.
  Variable x:A.

  Program Definition helper_ss_st (m:nat) 
          (pr : (braun_tree A (m+1) * (braun_tree A m)))
  : C ((braun_tree A (m+m+3)) * (braun_tree A (m+m+2))) 2 :=
    match pr with
      | (s,t) =>
        ( ++2 ;
          ret (Node x (m+1) (m+1) _ s s,
               Node x (m+1) m _ s t))
    end.
  
  Solve Obligations using (intros ; omega).

  Program Definition helper_st_tt (m:nat) 
          (pr : (braun_tree A (m+1) * (braun_tree A m)))
  : C ((braun_tree A (m+m+2)) * (braun_tree A (m+m+1))) 2 :=
    match pr with
      | (s,t) =>
        (++2 ;
         ret (Node x (m+1) m _ s t,
              Node x m m _ t t))
    end.

  Solve Obligations using (intros; omega).


  Lemma odd_cleanup : 
    forall k n, 
      odd n -> div2 n + (div2 n) + (1+k) = n + k.
    intros n k H.
    apply odd_double in H.
    unfold double in H.
    omega.
  Defined.

  Lemma even_cleanup : 
    forall k n,
      even n -> div2 n + (div2 n) + k = n + k.
    intros n k H.
    apply even_double in H.
    unfold double in H.
    omega.
  Defined.

  Definition copy_rt n := S (2 * fl_log n).

  Program Fixpoint copy2 (n:nat) {wf lt n}
  : C ((braun_tree A (n+1)) * (braun_tree A n)) 
      (copy_rt n) :=
    match n with 
      | 0 => (++1 ; ret (Node x 0 0 _ Empty Empty,Empty))
      | S n' => 
        match even_odd_dec n' with
          | right H =>
            p <- (copy2 (proj1_sig (odd_S2n n' H))) ;
              helper_ss_st p
          | left H =>
            p <- (copy2 (proj1_sig (even_2n n' H))) ;
              helper_st_tt p
        end
    end.

  Obligation 3. rewrite (odd_cleanup 2). omega. assumption. Defined.
  Obligation 4. rewrite (odd_cleanup 1). omega. assumption. Defined.

  Obligation 7. rewrite (even_cleanup 2). omega. assumption. Defined.
  Obligation 8. rewrite (even_cleanup 1). omega. assumption. Defined.

  Obligation 5.
    replace (fl_log (div2 n') + (fl_log (div2 n') + 0) + 2) 
      with ((fl_log (div2 n') + 1) + (fl_log (div2 n') + 1)) ; [| omega].
    rewrite fl_log_div2.
    unfold copy_rt.
    unfold mult.
    rewrite plus_0_r.
    reflexivity.
  Qed.

  Obligation 9.
    replace (fl_log (div2 n') + (fl_log (div2 n') + 0) + 2) 
    with ((fl_log (div2 n') + 1) + (fl_log (div2 n') + 1)) ; [| omega].
    rewrite fl_log_div2.
    unfold copy_rt.
    unfold mult.
    rewrite plus_0_r.
    reflexivity.
  Qed.

  Program Definition copy n : C (braun_tree A n) (copy_rt n) :=
    c <- (copy2 n) ;
    match c with
      | (t1,t2) => ret t2
    end.

  Solve Obligations using (intros; omega).

End copy2.
