Require Import List.
Require Import Braun.common.util Braun.common.le_util Braun.common.same_structure.
Require Import Braun.common.log Braun.common.big_oh.
Require Import Braun.monad.monad.
Require Import Program.
Require Import Omega.

Definition insert_at_time (n:nat) := 2 * n + 1.
Hint Unfold insert_at_time.

Definition InsertedAt {A:Set} (a:A) (n:nat) (l:list A) (res:list A) :=
  exists xs ys,
    l = xs ++ ys /\
    length xs = n /\
    res = xs ++ a :: ys.
Hint Unfold InsertedAt.

Program Fixpoint insert_at {A:Set} (a:A) (n:nat) (l:list A) (NV:n <= length l) :
  {! res !:! list A !<! c !>!
    InsertedAt a n l res /\
    c = insert_at_time n!}
  :=
  match n with
    | O =>
      += 1;
      <== (cons a l)
    | S n' =>
      match l with
        | nil =>
          _
        | cons a' l' =>
          res' <- insert_at a n' l' _ ;
          += 2 ;
          <== (cons a' res')
      end
  end.

Next Obligation.
Proof.
  unfold InsertedAt, insert_at_time.
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
  clear NV.
  rename n' into n.
  clear H2.
  rename H0 into REC_P.
  unfold insert_at_time.
  split; try omega.
  unfold InsertedAt in *.
  destruct REC_P as [xs [ys [EQl' [EQn EQres']]]].
  subst l' n res'.
  exists (a' :: xs). exists ys.
  simpl. eauto.
Qed.

Definition minsert_at_time (m:nat) (n:nat) := m * (insert_at_time n + 1) + 1.
Hint Unfold minsert_at_time.

Definition MInsertedAt {A:Set} (ma:list A) (n:nat) (l:list A) (res:list A) :=
  exists xs ys,
    l = xs ++ ys /\
    length xs = n /\
    res = xs ++ (rev ma) ++ ys.
Hint Unfold MInsertedAt.

Program Fixpoint minsert_at {A:Set} (ma:list A) (n:nat) (l:list A) (NV:n <= length l) :
  {! res !:! list A !<! c !>!
    MInsertedAt ma n l res /\
    c = minsert_at_time (length ma) n!}
  :=
  match ma with
    | nil =>
      += 1;
      <== l
    | cons a ma' =>
      res' <- insert_at a n l NV ;
      res'' <- minsert_at ma' n res' _ ;
      += 1 ;
      <== res''
  end.

Next Obligation.
Proof.
  unfold MInsertedAt.
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
  rename H into IA_P.
  destruct IA_P as [xs [ys [EQl' [EQn EQres']]]].
  subst l n res'.
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
  clear H4 H6.
  rename H0 into REC_P.
  rename H1 into IA_P.
  destruct IA_P as [xs [ys [EQl' [EQn EQres']]]].
  subst l n res'.
  destruct REC_P as [xsR [ysR [EQ1 [EQ2 EQ3]]]].
  subst res''.
  symmetry in EQ2.
  destruct (app_length_eq_both A xs (a :: ys) xsR ysR EQ2 EQ1) as [EQa EQb].
  subst xsR ysR.
  clear EQ2 EQ1.

  split.
  exists xs. exists ys.
  simpl. rewrite <- app_assoc. simpl.
  auto.

  clear NV.
  clear a ys.
  remember (length xs) as X. clear xs HeqX.
  remember (length ma') as M. clear ma' HeqM.
  clear A.
  unfold minsert_at_time.
  rewrite mult_succ_l.
  omega.
Qed.

Definition Zipper (A:Set) := ((list A) * (list A))%type.

Definition ZipperOf {A:Set} (l:list A) (z:Zipper A) :=
  let (xs, ys) := z in
    l = rev xs ++ ys.

Program Fixpoint to_zip {A:Set} (l:list A) :
  {! res !:! Zipper A !<! c !>!
    (fst res) = nil /\
    ZipperOf l res /\
    c = 1 !} :=
  += 1 ;
  <== (nil, l).

Program Fixpoint from_zip {A:Set} (z:Zipper A) (ALL_RIGHT:(fst z) = nil) :
  {! res !:! list A !<! c !>!
    ZipperOf res z /\
    c = 1 !} :=
  += 1 ;
  <== (snd z).

Next Obligation.
Proof.
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

Program Fixpoint zip_right {A:Set} (z:Zipper A) (SOME_RIGHT:(snd z) <> nil) :
  {! res !:! Zipper A !<! c !>!
    ZipperRight z res /\
    c = 1 !} :=
  match (snd z) with
    | nil =>
      _
    | cons a ys =>
      += 1 ;
      <== (a :: (fst z), ys)
  end.

Next Obligation.
Proof.
  congruence.
Defined.

Next Obligation.
Proof.
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

Program Fixpoint zip_left {A:Set} (z:Zipper A) (SOME_LEFT:(fst z) <> nil) :
  {! res !:! Zipper A !<! c !>!
    ZipperLeft z res /\
    c = 1 !} :=
  match (fst z) with
    | nil =>
      _
    | cons b xs =>
      += 1 ;
      <== (xs, b :: (snd z))
  end.

Next Obligation.
Proof.
  congruence.
Defined.

Next Obligation.
Proof.
 destruct z as [xs' ys].
 simpl in *.
 subst xs'.
 split; auto.
 unfold ZipperLeft.
 eauto.
Qed.

Definition ZipperInsert {A:Set} (z:Zipper A) (a:A) (res:Zipper A) :=
  res = ((fst z), a :: (snd z)).

Program Fixpoint zip_insert {A:Set} (z:Zipper A) (a:A) :
  {! res !:! Zipper A !<! c !>!
    ZipperInsert z a res /\
    c = 1 !} :=
  += 1 ;
  <== ((fst z), a :: (snd z)).

Next Obligation.
Proof.
  unfold ZipperInsert. auto.
Qed.

Definition ZipperRightN {A:Set} (z:Zipper A) (n:nat) (res:Zipper A) :=
  exists xs ys zs,
    z = (xs, ys ++ zs) /\
    length ys = n /\
    res = (((rev ys) ++ xs), zs).

Program Fixpoint zip_rightn {A:Set} (n:nat) (z:Zipper A) (NV:n <= length (snd z)) :
  {! res !:! Zipper A !<! c !>!
    ZipperRightN z n res /\
    c = 2 * n + 1 !} :=
  match n with
    | O =>
      += 1 ;
      <== z
    | S n' =>
      z' <- zip_right z _ ;
      z'' <- zip_rightn n' z' _ ;
      += 1 ;
      <== z''
  end.

Next Obligation.
Proof.
  split; auto.
  destruct z as [xs zs].
  exists xs. exists (@nil A). exists zs.
  simpl. auto.
Qed.

Next Obligation.
Proof.
  destruct (snd z) as [|a sz].
  simpl in NV. omega.
  congruence.
Qed.

Next Obligation.
Proof.
  rename H into ZR.
  destruct ZR as [xs [a [ys [EQz EQzr]]]].
  subst z z'. simpl in *.
  omega.
Qed.

Next Obligation.
Proof.
  clear H6 H4.
  rename H0 into ZRN.
  rename H1 into ZR.
  split; try omega.
  unfold ZipperRightN.
  destruct ZR as [xs [a [ys [EQz EQzr]]]].
  subst z z'. simpl in *.
  destruct ZRN as [xs' [ys' [zs' [EQ1 [EQ2 EQ3]]]]].
  subst n' z''.
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

Program Fixpoint zip_leftn {A:Set} (n:nat) (z:Zipper A) (NV:n <= length (fst z)) :
  {! res !:! Zipper A !<! c !>!
    ZipperLeftN z n res /\
    c = 2 * n + 1 !} :=
  match n with
    | O =>
      += 1 ;
      <== z
    | S n' =>
      z' <- zip_left z _ ;
      z'' <- zip_leftn n' z' _ ;
      += 1 ;
      <== z''
  end.

Next Obligation.
Proof.
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
  rename H into ZL.
  destruct ZL as [b [xs [ys [EQz EQzr]]]].
  subst z z'. simpl in *.
  omega.
Qed.

Next Obligation.
Proof.
  clear H6 H4.
  rename H0 into ZLN.
  rename H1 into ZL.
  split; try omega.
  unfold ZipperLeftN.
  destruct ZL as [b [xs [ys [EQz EQzr]]]].
  subst z z'. simpl in *.
  destruct ZLN as [xs' [ys' [zs' [EQ1 [EQ2 EQ3]]]]].
  subst n' z''.
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

Program Fixpoint zip_minsert {A:Set} (ma:list A) (z:Zipper A) :
  {! res !:! Zipper A !<! c !>!
    ZipperMInsert z ma res /\
    c = 2 * (length ma) + 1 !} :=
  match ma with
    | nil =>
      += 1 ;
      <== z
    | cons a ma' =>
      z' <- zip_insert z a ;
      z'' <- zip_minsert ma' z' ;
      += 1 ;
      <== z''
  end.

Next Obligation. 
Proof.
  unfold ZipperMInsert.
  simpl.
  destruct z as [xs ys].
  auto.
Qed.

Next Obligation.
Proof.
  clear H6 H4.
  rename H0 into ZMI.
  rename H1 into ZI.
  unfold ZipperMInsert, ZipperInsert in *.
  subst z'' z'.
  destruct z as [xs ys].
  simpl.
  rewrite <- app_assoc. simpl.
  split; auto.
  omega.
Qed.

Definition minsertz_at_time (m:nat) (n:nat) :=
  1 + (2 * n + 1) + (2 * m + 1) + (2 * n + 1) + 1.
Hint Unfold minsertz_at_time.

Program Fixpoint minsertz_at {A:Set} (ma:list A) (n:nat) (l:list A) (NV:n <= length l) :
  {! res !:! list A !<! c !>!
    MInsertedAt ma n l res /\
    c = minsertz_at_time (length ma) n!}
  :=
  z <- (to_zip l) ;
  zr <- (zip_rightn n z _) ;
  zr' <- (zip_minsert ma zr) ;
  z' <- (zip_leftn n zr' _) ;
  l' <- from_zip z' _ ;
  <== l'.

Next Obligation.
Proof.
  rename H into EQ.
  rename H0 into ZO.
  destruct z as [xs ys].
  simpl in *. subst xs.
  subst l.
  simpl in *.
  auto.
Qed.

Next Obligation.
Proof.
  rename H into ZMI.
  rename H1 into ZRN.
  destruct z as [xs ys].
  simpl in *.
  subst xs l.
  simpl in *.
  unfold ZipperMInsert in *.
  subst zr'.
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
  rename H6 into ZO.
  rename H3 into ZRN.
  rename H1 into ZMI.
  rename H into ZLN.

  destruct ZLN as [xsL [ysL [zsL [EQ1 [EQ2 EQ3]]]]].
  subst zr' n z'. simpl.
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
  auto.
Qed.

Next Obligation.
Proof.
  clear H18 H19 H16 H14 H12 H10.
  rename H4 into ZOl.
  rename H3 into EQfz.
  rename H2 into ZRN.
  rename H1 into ZMI.
  rename H0 into ZLN.
  rename H into ZOl'.

  destruct z as [xs ys]. simpl in *. subst xs.
  simpl in ZOl. subst l.
  destruct ZRN as [xsR [ysR [zsR [EQ1 [EQ2 EQ3]]]]].
  subst zr n.
  replace xsR with (@nil A) in *; try congruence.
  clear xsR.
  replace ys with (ysR ++ zsR) in *; try congruence.
  clear ys EQ1.
  destruct ZLN as [xsL [ysL [zsL [EQ1 [EQ2 EQ3]]]]].
  subst zr' z'.
  rewrite app_nil_r in *.
  unfold ZipperMInsert in ZMI.
  simpl in ZMI.
  replace zsL with (rev ma ++ zsR) in *; try congruence.
  clear zsL.
  inversion ZMI. clear ZMI.
  rename H0 into ZMI.
  unfold minsertz_at_time.
  split; [ | omega ].
  unfold ZipperOf in ZOl'.
  subst l'.
  rewrite app_assoc.
  rewrite <- rev_app_distr.
  rewrite ZMI.
  rewrite rev_involutive.
  exists ysR. exists zsR.
  auto.
Qed.

Theorem minsertz_is_better:
  forall m,
    0 < m ->
    big_oh (fun n => minsertz_at_time m n) (fun n => minsert_at_time m n).
Proof.
  intros m LT.
  unfold minsertz_at_time, minsert_at_time, insert_at_time.
  unfold big_oh.
  exists 0 5.
  intros n LE.
  replace (1 + (2 * n + 1) + (2 * m + 1) + (2 * n + 1) + 1) with
    (2 * m + 4 * n + 5); try omega.
  replace (5 * (m * (2 * n + 1 + 1) + 1)) with
    (10 * n * m + 10 * m + 5); try omega.

  destruct m as [|m]. omega.
  apply le_add.
  rewrite plus_comm.
  apply le_add.
  replace (4 * n) with (4 * n * 1); try omega.
  apply le_mult.
  omega. omega.
  omega. auto.
  clear LT LE.
  repeat rewrite mult_plus_distr_l.
  rewrite mult_1_r. rewrite mult_1_r.
  rewrite mult_assoc.
  rewrite mult_assoc.
  replace (5 * m * 2 * n) with (10 * n * m); try omega.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  rewrite (mult_comm m (2 * n)).
  rewrite mult_assoc.
  rewrite mult_assoc.
  rewrite mult_assoc.
  simpl.
  auto.
Qed.

