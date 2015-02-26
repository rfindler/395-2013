Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh Braun.common.pow.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.
Require Import Max.
Require Import Div2.
Require Import Relations_1.
Require Import Braun.clrs.rbtree.

Lemma height_log_case':
  forall
    (A : Set)
    (l : CTree A)
    (r : CTree A)
    (n : nat)
    (RBl : IsRB l n)
    (RBr : IsRB r n)
    (IHl : height l <= 2 * cl_log (count l + 1))
    (IHr : height r <= 2 * cl_log (count r + 1))
    (LEh : height r <= height l),
    S (height l) <= 2 * cl_log (count l + count r + 1 + 1).
Proof.
  intros.

  apply IsRB_impl_height_no_color in RBl.
  apply IsRB_impl_height_no_color in RBr.
  
  cut (2 * cl_log (count l + 1 + count l + 1) <= 2 * cl_log (count l + count r + 1 + 1)).
  intros LEc.
  eapply le_trans; [|apply LEc].
  rewrite <- cl_log_even.
  omega.
  apply le_mult. auto.
  apply cl_log_monotone.
  apply le_add; auto.
  replace (count l + 1 + count l) with (count l + count l + 1); try omega.
  apply le_add; auto.
  apply le_add; auto.

Admitted.

Lemma height_log_case:
  forall A (l r:CTree A) n,
    IsRB l n ->
    IsRB r n ->
    height l <= 2 * cl_log (count l + 1) ->
    height r <= 2 * cl_log (count r + 1) ->
    S (max (height l) (height r)) <= 2 * cl_log (count l + 1 + count r + 1).
Proof.
  intros A l r n RBl RBr IHl IHr.
  replace (count l + 1 + count r + 1 ) with (count l + count r + 1 + 1); try omega.

  eapply max_case_strong.
  apply height_log_case' with (n:=n); auto.
  replace (count l + count r + 1) with (count r + count l + 1); try omega.
  apply height_log_case' with (n:=n); auto.
Qed.

Lemma height_log_count:
  forall A (ct:CTree A) n,
    IsRB ct n ->
    height ct <= 2 * cl_log (count ct + 1).
Proof.
  intros A ct n IR.
  induction IR.

  simpl. auto.

  simpl (height (CT_node A l RED v r)).
  simpl (count (CT_node A l RED v r)).
  apply height_log_case with (n := n); auto.

  simpl (height (CT_node A l BLACK v r)).
  simpl (count (CT_node A l BLACK v r)).
  apply height_log_case with (n := n); auto.
Qed.

Lemma rb_black_heights_close:
  forall 
    (A : Set)
    (n : nat)
    (l : CTree A)    
    (IR1 : IsRB l n)
    (r : CTree A)
    (IR2 : IsRB r n),
   count l <= div2 (count l + count r).
Proof.
  induction n; intros Tl IRl Tr IRr.

  apply rb_black_height_0_count in IRl.
  apply rb_black_height_0_count in IRr.
  destruct (count Tl) as [|cTl].
  destruct (count Tr) as [|cTr].
  simpl. auto.
  replace cTr with 0 in *; try omega.
  replace cTl with 0 in *; try omega.
  destruct (count Tr) as [|cTr].
  simpl. admit. (* xxx false *)
  replace cTr with 0 in *; try omega.
  simpl. auto.

Admitted.

(* Finally, here is how CLRS puts it:

   Lemma 13.1: A red-black tree with n internal nodes has height at
   most 2 * lg(n + 1)

   This proof embeds the proof about a bound on the black-height.

 *)

(* Assuming we can do one of those, then we can prove this: *)

Lemma rb_black_height_impl_count:
  forall (A : Set)
    (ct : CTree A)
    (bh : nat)
    (IR : IsRB ct bh),
    bh <= cl_log (count ct + 1).
Proof.
  intros A ct bh IR.
  induction IR. omega.

  simpl.
  eapply le_trans. apply IHIR1.
  apply cl_log_monotone. omega.

  simpl.
  remember (count l) as L.
  remember (count r) as R.
  replace (L + 1 + R + 1) with (S (L + 1 + R)); try omega.
  rewrite cl_log_div2'.
  apply le_n_S.
  eapply le_trans.
  apply IHIR1.
  replace (L + 1) with (S L); try omega. simpl.
  rewrite cl_log_div2'.
  rewrite cl_log_div2'.
  apply le_n_S.
  apply cl_log_monotone.
  apply div2_monotone.
  apply le_n_S.

  subst L R. clear IHIR1 IHIR2 v.
  apply rb_black_heights_close with (n:=n); auto.
Qed.

