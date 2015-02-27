Require Import List.
Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.

Definition insert_at_time (n:nat) := 13 * n + 5.
Hint Unfold insert_at_time.

Definition InsertedAt {A:Set} (a:A) (n:nat) (l:list A) (res:list A) :=
  exists xs ys,
    l = xs ++ ys /\
    length xs = n /\
    res = xs ++ a :: ys.
Hint Unfold InsertedAt.

Definition insert_at_result (A:Set) (a:A) (n:nat) (l:list A) (NV:n <= length l) (res:list A) (c:nat) :=
  InsertedAt a n l res /\
  c = insert_at_time n.

Load "insert_at_gen.v".

Next Obligation.
Proof.
  unfold InsertedAt, insert_at_time, insert_at_result.
  simpl. split; auto.
  exists (@nil A). simpl. eauto.
Qed.

Next Obligation.
Proof.
  simpl in NV. omega.
Defined.

Next Obligation.
Proof.
  simpl in NV. omega.
Qed.

Next Obligation.
Proof.
  simpl in NV. omega.
Qed.

Next Obligation.
Proof.
  unfold insert_at_result in *.
  clear NV.
  clear H1 am.
  rename H0 into REC_P.
  unfold insert_at_time in *.
  destruct REC_P as [REC_P EQ].
  subst an.
  split; try omega.
  unfold InsertedAt in *.
  destruct REC_P as [xs [ys [EQl' [EQn EQres']]]].
  subst lp np resp.
  exists (ap :: xs). exists ys.
  simpl. eauto.
Qed.

Definition minsert_at_time (m:nat) (n:nat) := m * (insert_at_time n + 15) + 3.
Hint Unfold minsert_at_time.

Definition MInsertedAt {A:Set} (ma:list A) (n:nat) (l:list A) (res:list A) :=
  exists xs ys,
    l = xs ++ ys /\
    length xs = n /\
    res = xs ++ (rev ma) ++ ys.
Hint Unfold MInsertedAt.

Definition minsert_at_result (A:Set) (ma:list A) (n:nat) (l:list A) (NV:n <= length l) (res:list A) (c:nat) :=
  MInsertedAt ma n l res /\
  c = minsert_at_time (length ma) n.

Load "minsert_at_gen.v".

Next Obligation.
Proof.
  unfold minsert_at_result, MInsertedAt.
  split; auto.

  generalize l NV. clear l NV.
  induction n as [|n]; simpl; intros l NV.
  exists (@nil A). exists l.
  auto.
  destruct l as [|a l];
  simpl in *. omega.
  edestruct (IHn l) as [xs [ys [EQ1 [EQ2 EQ3]]]].
  omega.
  subst l n.
  exists (a :: xs). exists ys.
  simpl. auto.
Qed.

Next Obligation.
Proof.
  unfold insert_at_result in *.
  destruct H as [IA_P EQ]. subst am.
  destruct IA_P as [xs [ys [EQl' [EQn EQres']]]].
  subst l n resp.
  rewrite app_length in *.
  simpl.
  omega.
Qed.

Lemma app_length_eq_both:
  forall A (a b x y:list A),
    length a = length x ->
    a ++ b = x ++ y ->
    a = x /\ b = y.
Proof.
 induction a as [|aa a]; intros b [|xx x] y EQlen EQl; simpl in *.
 auto.
 congruence.
 congruence.
 edestruct (IHa b x y) as [EQa EQb].
 congruence.
 congruence.
 subst.
 inversion EQl.
 auto.
Qed.

Lemma app_length_eq:
  forall A (a b x y:list A),
    length a = length x ->
    a ++ b = x ++ y ->
    b = y.
Proof.
  intros A a b x y LEN EQ.
  destruct (app_length_eq_both A a b x y LEN EQ).
  auto.
Qed.

Next Obligation.
Proof.
  unfold minsert_at_result in *.
  unfold insert_at_result in *.
  clear am H3 am0 H2.
  rename H0 into REC_P.
  rename H1 into IA_P.
  destruct IA_P as [IA_P EQ]. subst an0.
  destruct REC_P as [REC_P EQ]. subst an.
  destruct IA_P as [xs [ys [EQl' [EQn EQres']]]].
  subst l n resp.
  destruct REC_P as [xsR [ysR [EQ1 [EQ2 EQ3]]]].
  subst respp.
  symmetry in EQ2.
  destruct (app_length_eq_both A xs (a :: ys) xsR ysR EQ2 EQ1) as [EQa EQb].
  subst xsR ysR.
  clear EQ2 EQ1.

  split.
  exists xs. exists ys.
  simpl. rewrite <- app_assoc. simpl.
  auto.

  clear NV.
  simpl.
  clear a ys.
  remember (length xs) as X. clear xs HeqX.
  remember (length map) as M. clear map HeqM.
  clear A.
  unfold minsert_at_time.
  rewrite mult_succ_l.
  omega.
Qed.

Definition Zipper (A:Set) := ((list A) * (list A))%type.

Definition ZipperOf {A:Set} (l:list A) (z:Zipper A) :=
  let (xs, ys) := z in
    l = rev xs ++ ys.

Definition to_zip_result (A:Set) (l:list A) (res:Zipper A) (c:nat) :=
  (fst res) = nil /\
  ZipperOf l res /\
  c = 3.

Load "to_zip_gen.v".

Next Obligation.
Proof.
  unfold to_zip_result. simpl. auto.
Qed.

Definition from_zip_result (A:Set) (z:Zipper A) (ALL_RIGHT:(fst z) = nil) (res:list A) (c:nat) :=
  ZipperOf res z /\
  c = 2.

Load "from_zip_gen.v".

Next Obligation.
Proof.
  unfold from_zip_result.
  destruct z as [xs ys].
  simpl in *. subst xs.
  program_simpl.
Qed.

Definition ZipperRight {A:Set} (z res:Zipper A) :=
  exists xs a ys,
    z = (xs, a :: ys) /\
    res = ((a :: xs), ys).

Lemma ZipperRight_same:
  forall A (z zr:Zipper A),
    ZipperRight z zr ->
    forall l,
      ZipperOf l z ->
      ZipperOf l zr.
Proof.
  unfold Zipper, ZipperRight, ZipperOf.
  intros A z zr ZR l ZO.
  destruct ZR as [xs [a [ys [EQz EQzr]]]].
  subst z zr.
  simpl.
  rewrite <- app_assoc.
  simpl. auto.
Qed.

Definition zip_right_result (A:Set) (z:Zipper A) (SOME_RIGHT:(snd z) <> nil) (res:Zipper A) (c:nat) :=
  ZipperRight z res /\
  c = 9.

Load "zip_right_gen.v".

Next Obligation.
Proof.
  congruence.
Defined.

Next Obligation.
Proof.
  unfold zip_right_result.
  destruct z as [xs ys'].
  simpl in *.
  subst ys'.
  split; auto.
  unfold ZipperRight.
  eauto.
Qed.

Definition ZipperLeft {A:Set} (z res:Zipper A) :=
  exists b xs ys,
    z = (b :: xs, ys) /\
    res = (xs, b :: ys).

Lemma ZipperLeft_same:
  forall A (z zl:Zipper A),
    ZipperLeft z zl ->
    forall l,
      ZipperOf l z ->
      ZipperOf l zl.
Proof.
  unfold Zipper, ZipperLeft, ZipperOf.
  intros A z zr ZR l ZO.
  destruct ZR as [b [xs [ys [EQz EQzr]]]].
  subst z zr.
  simpl in ZO.
  rewrite <- app_assoc in ZO.
  simpl in ZO. auto.
Qed.

Definition zip_left_result (A:Set) (z:Zipper A) (SOME_LEFT:(fst z) <> nil) (res:Zipper A) (c:nat) :=
  ZipperLeft z res /\
  c = 9.

Load "zip_left_gen.v".

Next Obligation.
Proof.
  congruence.
Defined.

Next Obligation.
Proof.
  unfold zip_left_result.
  destruct z as [xs' ys].
  simpl in *.
  subst xs'.
  split; auto.
  unfold ZipperLeft.
  eauto.
Qed.

Definition ZipperInsert {A:Set} (z:Zipper A) (a:A) (res:Zipper A) :=
  res = ((fst z), a :: (snd z)).

Definition zip_insert_result (A:Set) (z:Zipper A) (a:A) (res:Zipper A) (c:nat) :=
  ZipperInsert z a res /\
  c = 7.

Load "zip_insert_gen.v".

Next Obligation.
Proof.
  unfold zip_insert_result.
  unfold ZipperInsert. auto.
Qed.

Definition ZipperRightN {A:Set} (z:Zipper A) (n:nat) (res:Zipper A) :=
  exists xs ys zs,
    z = (xs, ys ++ zs) /\
    length ys = n /\
    res = (((rev ys) ++ xs), zs).

Definition zip_rightn_result (A:Set) (n:nat) (z:Zipper A) (NV:n <= length (snd z)) (res:Zipper A) (c:nat) :=
  ZipperRightN z n res /\
  c = 21 * n + 3.

Load "zip_rightn_gen.v".

Next Obligation.
Proof.
  unfold zip_rightn_result.
  split; auto.
  destruct z as [xs zs].
  exists xs. exists (@nil A). exists zs.
  simpl. auto.
Qed.

Next Obligation.
Proof.
  unfold zip_rightn_result.
  destruct (snd z) as [|a sz].
  simpl in NV. omega.
  congruence.
Qed.

Next Obligation.
Proof.
  unfold zip_right_result in *.
  rename H into ZR.
  destruct ZR as [[xs [a [ys [EQz EQzr]]]] EQ].
  subst z zp. simpl in *.
  omega.
Qed.

Next Obligation.
Proof.
  unfold zip_rightn_result in *.
  unfold zip_right_result in *.
  clear am am0 H2 H3.
  rename H0 into ZRN.
  rename H1 into ZR.
  destruct ZRN as [ZRN EQ]. subst an.
  destruct ZR as [ZR EQ]. subst an0.
  split; try omega.
  unfold ZipperRightN.
  destruct ZR as [xs [a [ys [EQz EQzr]]]].
  subst z zp. simpl in *.
  destruct ZRN as [xs' [ys' [zs' [EQ1 [EQ2 EQ3]]]]].
  subst np zpp.
  replace xs' with (a :: xs) in *; try congruence.
  clear  xs' NV.
  replace ys with (ys' ++ zs') in *; try congruence.
  clear EQ1 ys.
  exists xs. exists (a :: ys'). exists zs'.
  simpl.
  rewrite <- app_assoc. simpl.
  auto.
Qed.

Definition ZipperLeftN {A:Set} (z:Zipper A) (n:nat) (res:Zipper A) :=
  exists xs ys zs,
    z = (ys ++ xs, zs) /\
    length ys = n /\
    res = (xs, (rev ys) ++ zs).

Definition zip_leftn_result (A:Set) (n:nat) (z:Zipper A) (NV:n <= length (fst z)) (res:Zipper A) (c:nat) :=
  ZipperLeftN z n res /\
  c = 21 * n + 3.

Load "zip_leftn_gen.v".

Next Obligation.
Proof.
  unfold zip_leftn_result.
  split; auto.
  destruct z as [xs zs].
  exists xs. exists (@nil A). exists zs.
  simpl. auto.
Qed.

Next Obligation.
Proof.
  destruct (fst z) as [|a sz].
  simpl in NV. omega.
  congruence.
Qed.

Next Obligation.
Proof.
  unfold zip_left_result in *.
  rename H into ZL.
  destruct ZL as [[b [xs [ys [EQz EQzr]]]] EQ].
  subst z zp. simpl in *.
  omega.
Qed.

Next Obligation.
Proof.
  unfold zip_left_result in *.
  unfold zip_leftn_result in *.
  clear am H3 H2 am0.
  rename H0 into ZLN.
  rename H1 into ZL.
  destruct ZLN as [ZLN EQ]. subst an.
  destruct ZL as [ZL EQ]. subst an0.
  split; try omega.
  unfold ZipperLeftN.
  destruct ZL as [b [xs [ys [EQz EQzr]]]].
  subst z zp. simpl in *.
  destruct ZLN as [xs' [ys' [zs' [EQ1 [EQ2 EQ3]]]]].
  subst np zpp.
  replace zs' with (b :: ys) in *; try congruence.
  clear zs' NV.
  replace xs with (ys' ++ xs') in *; try congruence.
  clear EQ1 xs.
  exists xs'. exists (b :: ys'). exists ys.
  simpl.
  rewrite <- app_assoc. simpl.
  auto.
Qed.

Definition ZipperMInsert {A:Set} (z:Zipper A) (ma:list A) (res:Zipper A) :=
  res = ((fst z), (rev ma) ++ (snd z)).

Definition zip_minsert_result (A:Set) (ma:list A) (z:Zipper A) (res:Zipper A) (c:nat) :=
  ZipperMInsert z ma res /\
  c = 18 * (length ma) + 3.

Load "zip_minsert_gen.v".

Next Obligation. 
Proof.
  unfold zip_minsert_result.
  unfold ZipperMInsert.
  simpl.
  destruct z as [xs ys].
  auto.
Qed.

Next Obligation.
Proof.
  unfold zip_minsert_result in *.
  unfold zip_insert_result in *.
  clear am H3 am0 H2.
  rename H0 into ZMI.
  rename H1 into ZI.
  destruct ZMI as [ZMI EQ]. subst an.
  destruct ZI as [ZiI EQ]. subst an0.
  unfold ZipperMInsert, ZipperInsert in *.
  subst zpp zp.
  destruct z as [xs ys].
  split. simpl. rewrite <- app_assoc. simpl. auto.
  simpl length.
  omega.
Qed.

Definition minsertz_at_time (m:nat) (n:nat) :=
  3 + (21 * n + 3) + (18 * m + 3) + (21 * n + 3) + 2 + 22.
Hint Unfold minsertz_at_time.

Definition minsertz_at_result (A:Set) (ma:list A) (n:nat) (l:list A) (NV:n <= length l) (res:list A) (c:nat) :=
  MInsertedAt ma n l res /\
  c = minsertz_at_time (length ma) n.

Load "minsertz_at_gen.v".

Next Obligation.
Proof.
  unfold to_zip_result in *.
  destruct H as [EQ [ZO EQam]].
  destruct z as [xs ys].
  simpl in *. subst xs.
  subst l.
  simpl in *.
  auto.
Qed.

Next Obligation.
Proof.
  unfold to_zip_result in *.
  destruct H1 as [EQ [ZO EQam]].
  unfold zip_rightn_result in *.
  destruct H0 as [ZRN EQam0].
  unfold zip_minsert_result in *.
  destruct H as [ZMI EQam1].
  subst.
  destruct z as [xs ys].
  simpl in *.
  subst xs l.
  simpl in *.
  unfold ZipperMInsert in *.
  subst zrp.
  unfold ZipperRightN in *.
  destruct ZRN as [xs' [ys' [z' [EQ1 [EQ2 EQ3]]]]].
  subst zr n.
  simpl.
  rewrite app_length.
  rewrite rev_length.
  omega.
Qed.

Next Obligation.
Proof.
  unfold to_zip_result in *.
  unfold zip_rightn_result in *.
  unfold zip_minsert_result in *.
  unfold zip_leftn_result in *.
  destruct H2 as [EQ [ZO EQam]].
  destruct H1 as [ZRN EQam0].
  destruct H0 as [ZMI EQam1].
  destruct H as [ZLN EQam2].
  subst.

  destruct ZLN as [xsL [ysL [zsL [EQ1 [EQ2 EQ3]]]]].
  subst zrp n zp. simpl.
  destruct ZRN as [xsR [ysR [zsR [EQ1 [EQ2 EQ3]]]]].
  subst zr z. simpl.
  unfold ZipperMInsert in *.
  simpl in ZMI.
  replace zsL with ((rev ma) ++ zsR) in *; try congruence.
  clear zsL.
  rewrite <- rev_length in EQ2.
  inversion ZMI. rename H0 into EQapp.
  edestruct app_length_eq_both.
  apply EQ2.
  symmetry.
  apply EQapp.
  subst xsL.
  auto.
Qed.

Next Obligation.
Proof.
  unfold to_zip_result in *.
  unfold zip_rightn_result in *.
  unfold zip_minsert_result in *.
  unfold zip_leftn_result in *.
  unfold from_zip_result in *.
  unfold minsertz_at_result.
  clear am am0 am1 am2 am3 H9 H8 H7 H6 H5.
  destruct H4 as [EQfz [ZOl EQan3]].
  destruct H3 as [ZRN EQan2].
  destruct H2 as [ZMI EQan1].
  destruct H1 as [ZLN EQan0].
  destruct H0 as [ZOlp EQan].
  subst.

  destruct z as [xs ys]. simpl in EQfz. subst xs.
  simpl in ZOl. subst l.
  destruct ZRN as [xsR [ysR [zsR [EQ1 [EQ2 EQ3]]]]].
  subst zr n.
  replace xsR with (@nil A) in *; try congruence.
  clear xsR.
  replace ys with (ysR ++ zsR) in *; try congruence.
  clear ys EQ1.
  destruct ZLN as [xsL [ysL [zsL [EQ1 [EQ2 EQ3]]]]].
  subst zrp zp.
  rewrite app_nil_r in *.
  unfold ZipperMInsert in ZMI.
  simpl in ZMI.
  replace zsL with (rev ma ++ zsR) in *; try congruence.
  clear zsL.
  inversion ZMI. clear ZMI.
  rename H0 into ZMI.
  split.
  
  unfold ZipperOf in ZOlp.
  subst lp.
  rewrite app_assoc.
  rewrite <- rev_app_distr.
  rewrite ZMI.
  rewrite rev_involutive.
  exists ysR. exists zsR.
  auto.

  unfold minsertz_at_time.
  omega.
Qed.

Definition minsertz_at_time_clean m n :=
  (0 * n * m) + (18 * m) + (42 * n) + 36.

Lemma minsertz_at_time_clean_eq:
  forall m n,
    minsertz_at_time m n =
    minsertz_at_time_clean m n.
Proof.
  unfold minsertz_at_time_clean, minsertz_at_time.
  intros m n.
  rewrite mult_0_l.
  omega.
Qed.

Definition minsert_at_time_clean m n :=
  (13 * n * m) + (20 * m) + (0 * n) + 3.

Lemma minsert_at_time_clean_eq:
  forall m n,
    minsert_at_time_clean m n =
    minsert_at_time m n.
Proof.
  unfold minsert_at_time_clean, minsert_at_time, insert_at_time.
  intros m n.
  rewrite mult_0_l.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_l.
  rewrite mult_comm.
  omega.
Qed.

Theorem minsertz_is_better:
  forall m,
    0 < m ->
    big_oh (fun n => minsertz_at_time m n) (fun n => minsert_at_time m n).
Proof.
  intros m LT.
  eapply big_oh_trans.
  apply big_oh_eq. apply minsertz_at_time_clean_eq.
  eapply big_oh_trans; [ | apply big_oh_eq; apply minsert_at_time_clean_eq ].
  unfold minsertz_at_time_clean, minsert_at_time_clean.
  unfold big_oh.
  exists 0 12.
  intros n LE.
  clear LE.

  destruct m as [|m]. omega.
  clear LT.
  rewrite mult_plus_distr_l.
  apply le_add; [ | omega ].
  replace (0 * n * S m + 18 * S m + 42 * n) with
    (0 * n * S m + 42 * n + 18 * S m); try omega.
  replace (13 * n * S m + 20 * S m + 0 * n) with
    (13 * n * S m + 0 * n + 20 * S m); try omega.
  rewrite mult_plus_distr_l.
  apply le_add; [ | omega ].
  rewrite mult_0_l. rewrite plus_0_l.
  rewrite mult_0_l. rewrite plus_0_r.  
  rewrite <- mult_assoc.
  rewrite mult_assoc with (n := 12).
  replace (12 * 13) with 156; try auto.  
  rewrite mult_comm with (n := n).
  rewrite mult_assoc.
  rewrite mult_succ_r.
  rewrite mult_plus_distr_r.
  replace (42 * n) with (0 + 42 * n); try omega.
  apply le_add.
  apply le_0_n.
  omega.
Qed.

