Require Import Braun.omonad.braun Braun.omonad.util Braun.omonad.monad Braun.omonad.log.
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

  Definition copy_rt n := S (2 * fl_log n).

  Program Fixpoint copy2 (n:nat) {wf lt n}
  : C ((braun_tree A (n+1)) * (braun_tree A n)) 
      (copy_rt n) :=
    match n with 
      | 0 => (++1 ; ret (Node x 0 0 _ Empty Empty,Empty))
      | S n' => 
        if even_odd_dec n' 
        then (p <- (copy2 (div2 n'));
              helper_st_tt p)
        else (p <- (copy2 (div2 n'));
              helper_ss_st p)
    end.

  Obligation 3. rewrite (even_cleanup 2); [omega|assumption]. Defined.
  Obligation 4. rewrite (even_cleanup 1); [omega|assumption]. Defined.

  Obligation 7. rewrite (odd_cleanup 2); [omega|assumption]. Defined.
  Obligation 8. rewrite (odd_cleanup 1); [omega|assumption]. Defined.

  Obligation 5.
    replace (fl_log (div2 n') + (fl_log (div2 n') + 0) + 2) 
      with ((fl_log (div2 n') + 1) + (fl_log (div2 n') + 1)) ; [| omega].
    rewrite fl_log_div2; unfold copy_rt; omega.
  Qed.

  Obligation 9.
    replace (fl_log (div2 n') + (fl_log (div2 n') + 0) + 2) 
    with ((fl_log (div2 n') + 1) + (fl_log (div2 n') + 1)) ; [| omega].
    rewrite fl_log_div2; unfold copy_rt; omega.
  Qed.

  Program Definition copy n : C (braun_tree A n) (copy_rt n) :=
    c <- (copy2 n) ;
    match c with
      | (t1,t2) => ret t2
    end.

  Solve Obligations using (intros; omega).

End copy2.
