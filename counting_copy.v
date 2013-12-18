Require Import braun util monad.
Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax.

Set Implicit Arguments.

Section copy2.

  Variable A:Set.
  Variable x:A.

Program Definition helper_ss_st (m:nat) 
        (pr : (braun_tree A (m+1) * (braun_tree A m)))
: C ((braun_tree A (m+m+3)) * (braun_tree A (m+m+2))) :=
  match pr with
    | (s,t) =>
      ( ++2 ;
        ret (Node x (m+1) (m+1) _ s s,
             Node x (m+1) m _ s t))
  end.

Solve Obligations using (intros ; omega).

Program Definition helper_st_tt (m:nat) 
        (pr : (braun_tree A (m+1) * (braun_tree A m)))
: C ((braun_tree A (m+m+2)) * (braun_tree A (m+m+1))) :=
  match pr with
    | (s,t) =>
      ( ++2 ;
        ret (Node x (m+1) m _ s t,
             Node x m m _ t t))
  end.

Solve Obligations using (intros; omega).

Program Fixpoint copy2 (n:nat) {wf lt n}
  : C ((braun_tree A (n+1)) * (braun_tree A n)) :=
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

Obligation 3. rewrite (odd_cleanup 2). omega. assumption. Defined.
Obligation 4. rewrite (odd_cleanup 1). omega. assumption. Defined.

Obligation 6. rewrite (even_cleanup 2). omega. assumption. Defined.
Obligation 7. rewrite (even_cleanup 1). omega. assumption. Defined.

Definition copy n :=
  c <- (copy2 n) ;
  match c with
      | (t1,t2) => ret t2
  end.

(* fl_log *)
Program Fixpoint fl_log n {wf lt n} : nat :=
  match n with
    | 0 => 0
    | S n' => S (fl_log (div2 n'))
  end.

Section map.
  Variables P Q : Type.
  Variable f : P -> Q.

  Fixpoint map (s : list P) : list Q :=
    match s with
      | nil => nil
      | cons h t => cons (f h) (map t)
    end.
End map.

Example rs_ex :
  map fl_log
    [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15]
  = [0;1;1;2;2;2;2;3;3;3;3; 3; 3; 3; 3; 4]%list.
compute. reflexivity.
Qed.
(* end fl_log *)

Definition rt (n : nat) := S (2 * fl_log n).

Program Example copy_example :
  time (copy 2)
  = rt 2.
compute; reflexivity.
Qed.

Program Example copy_example2 :
  time (copy 24)
  = rt 24.
compute; reflexivity.
Qed.

Program Example copy_example3 :
  time (copy 53)
  = rt 53.
compute; reflexivity.
Qed.

Program Example copy_example4 :
  time (copy 109)
  = rt 109.
compute; reflexivity.
Qed.

Program Definition copy2_Sn_even_body (n:nat) (H: even n)
: C ((braun_tree A ((S n)+1)) * (braun_tree A (S n))) :=
  (p <- (copy2 (proj1_sig (even_2n n H))) ;
   helper_st_tt p).

Obligation 1. rewrite (even_cleanup 2). omega. assumption. Defined.
Obligation 2. rewrite (even_cleanup 1). omega. assumption. Defined.

Lemma copy2_even : forall n (H: even n), 
            copy2 (S n) = copy2_Sn_even_body H.
  intros.
(*
  rewrite (Fix_eq _ lt lt_wf (fun n => C ((braun_tree A ((S n)+1)) * (braun_tree A (S n))))).
*)
Admitted.

Program Definition copy2_Sn_odd_body (n:nat) (H: odd n)
: C ((braun_tree A ((S n)+1)) * (braun_tree A (S n))) :=
  (p <- (copy2 (proj1_sig (odd_S2n n H))) ;
   helper_ss_st p).

Obligation 1. rewrite (odd_cleanup 2). omega. assumption. Defined.
Obligation 2. rewrite (odd_cleanup 1). omega. assumption. Defined.

Lemma copy2_odd : forall n (H: odd n), 
            copy2 (S n) = copy2_Sn_odd_body H.
  intros.
(*
  rewrite (Fix_eq _ lt lt_wf (fun n => C ((braun_tree A ((S n)+1)) * (braun_tree A (S n))))).
*)
Admitted.

Lemma helper_st_tt_time : 
  forall m (pr : (braun_tree A (m+1) * (braun_tree A m))),
    snd (helper_st_tt pr) = 2.
  unfold helper_st_tt.
  unfold time.
  intros.
  simpl.
  destruct pr.
  reflexivity.
Qed.

Lemma helper_ss_st_time : 
  forall m (pr : (braun_tree A (m+1) * (braun_tree A m))),
    snd (helper_ss_st pr) = 2.
  unfold helper_ss_st.
  unfold time.
  intros.
  simpl.
  destruct pr.
  reflexivity.
Qed.

Lemma fl_log_div2': forall n, fl_log (S n) = S (fl_log (div2 n)).
  intros.
  apply (Fix_eq _ lt lt_wf (fun _ => nat)).
  intuition.
  destruct x0; [ reflexivity | repeat f_equal].
Qed.

Lemma fl_log_div2 : forall n, fl_log (div2 n) + 1 = fl_log (S n).
  intros n.
  rewrite fl_log_div2'.
  intuition.
Qed.

Lemma copy2_running_time :
  forall (n:nat),
    time (copy2 n) = rt n.
  apply (well_founded_ind 
           lt_wf 
           (fun n => (time (copy2 n) = rt n))).
  intros n IND.
  destruct n.
  compute. reflexivity.

  remember (even_odd_dec n) as EO; inversion EO; clear EO HeqEO.
  rewrite (copy2_even H).
  unfold copy2_Sn_even_body. simpl.
  remember (copy2 (div2 n)) as R.
  destruct R.

  assert (n0 = time (copy2 (div2 n))) as N0RES; [
    simpl in HeqR;
    inversion HeqR;
    intuition |
    rewrite N0RES; clear N0RES].
  rewrite IND; [| apply lt_div2'].
  simpl.

  rewrite (helper_st_tt_time p).

  replace (fl_log (div2 n) + (fl_log (div2 n) + 0) + 2) 
          with ((fl_log (div2 n) + 1) + (fl_log (div2 n) + 1)) ; [| omega].
  rewrite fl_log_div2.
  unfold rt.
  unfold mult.
  rewrite plus_0_r.
  reflexivity.

  rewrite (copy2_odd H).
  unfold copy2_Sn_odd_body. simpl.
  remember (copy2 (div2 n)) as R.
  destruct R.

  assert (n0 = time (copy2 (div2 n))) as N0RES; [
    simpl in HeqR;
    inversion HeqR;
    intuition |
    rewrite N0RES; clear N0RES].
  rewrite IND; [| apply lt_div2'].
  simpl.

  rewrite (helper_ss_st_time p).

  replace (fl_log (div2 n) + (fl_log (div2 n) + 0) + 2) 
          with ((fl_log (div2 n) + 1) + (fl_log (div2 n) + 1)) ; [| omega].
  rewrite fl_log_div2.
  unfold rt.
  unfold mult.
  rewrite plus_0_r.
  reflexivity.
Qed.

Theorem copy_running_time :
  forall (n:nat),
    time (copy n) = rt n.
  intros n.
  unfold copy.
  remember (copy2 n) as W.
  destruct W as [tn1 tn].
  unfold ret.
  unfold bind.
  destruct tn1.
  simpl.

  assert (time (copy2 n) = tn).
  destruct (copy2 n).
  inversion HeqW.
  simpl.
  reflexivity.

  rewrite copy2_running_time in H.
  intuition.
Qed.

End copy2.
