Set Implicit Arguments.
Require Import braun util monad.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax.

Program Definition helper_ss_st (A:Set) (x:A) (m:nat) 
        (pr : (braun_tree A (m+1) * (braun_tree A m)))
: C ((braun_tree A (2*m+3)) * (braun_tree A (2*m+2))) :=
  match pr with
    | (s,t) =>
      ( ++2 ;
        ret (Node x (m+1) (m+1) _ s s,
             Node x (m+1) m _ s t))
  end.

Solve Obligations using (intros ; omega).

Program Definition helper_st_tt (A:Set) (x:A) (m:nat) 
        (pr : (braun_tree A (m+1) * (braun_tree A m)))
: C ((braun_tree A (2*m+2)) * (braun_tree A (2*m+1))) :=
  match pr with
    | (s,t) =>
      ( ++2 ;
        ret (Node x (m+1) m _ s t,
             Node x m m _ t t))
  end.

Solve Obligations using (intros; omega).

Program Definition copy2 (A:Set) (x:A) : forall n, C ((braun_tree A (n+1)) * (braun_tree A n)) :=
  Fix lt_wf _
      (fun n copy2 => 
         match n with 
           | 0 => (++1 ; ret (Node x 0 0 _ Empty Empty, Empty))
           | S n' => 
             match even_odd_dec n' with
               | right H =>
                 p <- (copy2 (proj1_sig (odd_S2n n' H)) _) ;
                 helper_ss_st x p
               | left H =>
                 p <- (copy2 (proj1_sig (even_2n n' H)) _) ;
                 helper_st_tt x p
             end
         end).

Lemma odd_cleanup : 
  forall n k, 
    odd n -> div2 n + (div2 n + 0) + (k + 1) = n + k.
  intros n k H.
  apply odd_double in H.
  unfold double in H.
  omega.
Defined.

Lemma even_cleanup : 
  forall n k,
    even n -> div2 n + (div2 n + 0) + k = n + k.
  intros n k H.
  apply even_double in H.
  unfold double in H.
  omega.
Defined.

Obligation 3. rewrite (odd_cleanup 2). omega. assumption. Defined.
Obligation 4. rewrite (odd_cleanup 1). omega. assumption. Defined.

Obligation 6. rewrite (even_cleanup 2). omega. assumption. Defined.
Obligation 7. rewrite (even_cleanup 1). omega. assumption. Defined.

Definition copy (A:Set) (x:A) n :=
  c <- (copy2 x n) ;
  ret (snd c).



(* fl_log *)
Program Fixpoint fl_log n {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S n' => S (fl_log (div2 n'))
  end.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  Fixpoint map (s : list A) : list B :=
    match s with
      | nil => nil
      | cons h t => cons (f h) (map t)
    end.
End map.

Example rs_ex :
  map
    fl_log
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
  = [0;1;1;2;2;2;2;3;3;3;3; 3; 3; 3; 3; 4]%list.
compute. reflexivity.
Qed.
(* end fl_log *)



Definition rt (n : nat) := S (2 * fl_log n).

Program Example copy_example :
  time (copy 0 2)
  = rt 2.
compute; reflexivity.
Qed.

Program Example copy_example2 :
  time (copy 0 24)
  = rt 24.
compute; reflexivity.
Qed.

Program Example copy_example3 :
  time (copy 0 53)
  = rt 53.
compute; reflexivity.
Qed.

Program Example copy_example4 :
  time (copy 0 109)
  = rt 109.
compute; reflexivity.
Qed.



Section copy2.
  Variable A:Set.
  Variable x:A.


  Program Definition copy2_Sn_body (n:nat) : C ((braun_tree A ((S n)+1)) * (braun_tree A (S n))) :=
    match even_odd_dec n with
      | right H =>
        p <- (copy2 x (proj1_sig (odd_S2n n H))) ;
          helper_ss_st x p
      | left H =>
        p <- (copy2 x (proj1_sig (even_2n n H))) ;
          helper_st_tt x p
    end.

  Obligation 1. rewrite (odd_cleanup 2). omega. assumption. Defined.
  Obligation 2. rewrite (odd_cleanup 1). omega. assumption. Defined.
  
  Obligation 3. rewrite (even_cleanup 2). omega. assumption. Defined.
  Obligation 4. rewrite (even_cleanup 1). omega. assumption. Defined.

  
  Program Lemma copy2_Sn_reduce :
    forall (n:nat),
      copy2 x (S n) = copy2_Sn_body n.
  intros.
  unfold copy2.
  unfold Fix.
  unfold Fix_F.
  unfold copy2_Sn_body.
(*
  apply (Fix_eq _ lt (lt_wf) (fun n => C ((braun_tree A (n+1)) * (braun_tree A n)))).
*)
  Admitted.


Lemma copy2_running_time :
  forall (n:nat),
    time (copy2 x n) = rt n.
  intros.
  apply (well_founded_ind 
           lt_wf 
           (fun n => (time (copy2 x n) = rt n))).
  intros.
  destruct x0.
  compute. reflexivity.
  unfold copy2.
  Admitted.

Theorem copy_running_time :
  forall (n:nat),
    time (copy x n) = rt n.
  Admitted.


End copy2.
