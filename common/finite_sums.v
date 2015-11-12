Require Import Program Div2 Omega.
Require Import Arith Arith.Even Arith.Div2 NPeano.
Require Import Coq.Program.Wf Init.Wf.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Mult.
Require Import Coq.Lists.List.
Require Import Braun.common.log.

Notation "x ?= y" := (nat_compare x y).

Fixpoint listfrom_acc (i count : nat) : list nat :=
  match count with
    | 0 => []
    | S c => i :: (listfrom_acc (S i) c)
  end.

Definition listfrom (i j : nat) : list nat := listfrom_acc i (S j - i).

Lemma listfrom_i_i : forall i, listfrom i i = [i].
Proof.
  intros.
  unfold listfrom.
  assert (S i - i = 1); try omega. rewrite H. simpl. auto.
Qed.

Lemma listfrom_S : forall i j, i < j -> listfrom i j = i :: listfrom (S i) j.
Proof.
  intros.
  unfold listfrom.
  remember (S j -i) as k.
  destruct k. intuition.
  simpl. assert (k = j - i). omega. rewrite H0. auto.
Qed.

Fixpoint sumlist (l : list nat) : nat :=
  match l with
    | [] => 0
    | h :: t => h + sumlist t
  end.

(*
Lemma listfrom_splits : forall i j k, i <= j -> j < k -> listfrom i k = listfrom i j ++ listfrom (S j) k.
*)


Fixpoint sum (i j : nat) (f : nat -> nat) : nat :=
  match (nat_compare i j) with
  | Lt => match j with
               | 0 => 0
               | S j' => sum i j' f + f j
             end
  | Eq => f i
  | Gt => 0
  end.


Lemma sum_gt : forall i j f, i > j -> sum i j f = 0.
Proof.
  intros.
  destruct i. inversion H. 
  destruct j. simpl. auto.
  simpl. assert ((i ?= j) = Gt). apply nat_compare_gt. omega.
  rewrite H0. auto.
Qed.

Lemma sum_eq :
  forall i f, sum i i f = f i.
Proof.
  intros.
  induction i.
  auto.
  simpl. 
  assert ((i ?= i) = Eq). apply nat_compare_eq_iff. auto. rewrite H. auto.
Qed. 


Lemma sum_S_j :
  forall i j f,
  i < S j ->
  sum i (S j) f = sum i j f + f (S j).
Proof.
intros.
simpl.
rewrite nat_compare_lt in H.
rewrite H.
auto.
Qed.

Lemma sum_adds_0 :
  forall j f, sum 0 j f = f 0 + sum 1 j f.
Proof.
intros.
apply (well_founded_ind
          lt_wf
          (fun j =>  sum 0 j f = f 0 + sum 1 j f)).
intros.
destruct x. simpl. omega.
simpl.
destruct x. simpl. auto.
 rewrite plus_assoc. rewrite <- H. auto. auto.
Qed.

Definition shift (f : nat -> nat) : nat -> nat := (fun n => f (S n)).
Definition shift_by (k : nat) (f : nat -> nat) : nat -> nat := (fun n => f (n + k)).

Lemma shift_by_0 : forall f n, shift_by 0 f n= f n.
Proof. intros. unfold shift_by. rewrite plus_0_r. auto.
Qed.

Lemma shift_by_S : forall f n k, shift_by (S k) f n = shift (shift_by k f) n.
Proof.
  intros.
  unfold shift_by.
  unfold shift.
  assert (n + S k = S n + k);[omega|].
  rewrite H. auto.
Qed.

Lemma sum_shifts :
  forall i j f, sum (S i) (S j) f = sum i j (shift f).
Proof.
intros.
remember (nat_compare i j) as H.
destruct H. 
apply eq_sym in HeqH. simpl.
rewrite HeqH.
apply nat_compare_eq in HeqH.
rewrite HeqH. destruct j. simpl. auto. simpl. 
assert ( (j ?= j) = Eq). 
apply nat_compare_eq_iff. auto. rewrite H. auto.

assert (i < j).
apply nat_compare_lt. auto.
apply (well_founded_ind lt_wf (fun j => forall i f, i < j -> sum (S i) (S j) f = sum i j (shift f))); auto.
intros. destruct H1.

rewrite sum_S_j; try omega.
assert  ((i0 ?= i0) = Eq). apply nat_compare_eq_iff. auto. simpl. rewrite H1. 
assert ((i0 ?= S i0) = Lt). apply nat_compare_lt. auto. rewrite H2. simpl.
simpl. rewrite sum_eq. auto.
rewrite sum_S_j; try omega.
rewrite H0; try omega; auto. 
rewrite sum_S_j; try omega.
auto.

apply eq_sym in HeqH.
simpl. rewrite HeqH.
 destruct i. destruct j.
inversion HeqH. inversion HeqH. destruct j.
simpl. auto. simpl.
assert (S i > S j);try  apply nat_compare_gt; auto.
assert (i > j); try omega.
assert ((i ?= j) = Gt); try apply nat_compare_gt; auto.
rewrite H1. auto.
Qed.



Lemma sum_adds :
  forall i j f, i <= j -> sum i j f = f i + sum (S i) j f.
Proof.
intros i j.
apply (lt_wf_double_ind
          (fun i j =>forall f : nat -> nat, i <= j -> sum i j f = f i + sum (S i) j f)).
intros.
destruct n. apply sum_adds_0.
destruct m. inversion H1.
rewrite sum_shifts.
rewrite H; try omega.
assert (sum (S (S n)) (S m) f = sum (S n) m (shift f)).
apply sum_shifts.
rewrite H2.
unfold shift. auto.
Qed.

Lemma sum_inc : forall i j k f, i < k -> k < j -> sum k j f <= sum i j f.
Proof.
  intros.
  apply (well_founded_ind lt_wf (fun k => forall i j f, i<k -> k<j -> sum k j f <= sum i j f)); auto.
clear.
intros.
  inversion H0.
  replace (sum (S i) j f) with (0 + sum (S i) j f);[|omega].
  replace (sum i j f) with (f i + sum (S i) j f).
  apply plus_le_compat; omega.
  apply eq_sym.
  apply sum_adds. omega.
  apply (le_trans (sum (S m) j f)
                           (sum m j f)).
 replace (sum (S m) j f) with (0 + sum (S m) j f);[|omega].
  replace (sum m j f) with (f m + sum (S m) j f).
  apply plus_le_compat; omega.
  apply eq_sym.
  apply sum_adds. omega.
apply H. omega. omega. omega.
Qed.

Lemma sum_constant :
  forall i j n k, i + k = j -> sum i j (fun _ => n) = (k + 1)*n.
Proof.
  intros.
  apply (well_founded_ind lt_wf (fun k => forall i j,  i + k = j -> sum i j (fun _ => n) = (k + 1)*n)); auto.
  clear.
  intros.
  destruct x.
   simpl. rewrite plus_0_r. assert (i=j); try omega. rewrite H1. rewrite sum_eq. auto.
  assert (i < j); try omega.
  rewrite sum_adds; auto.
  rewrite mult_plus_distr_r. rewrite mult_1_l.
  rewrite H with (y:= x); try omega. replace (x+1) with (S x); omega. omega.
Qed.

Definition const (n: nat) : nat -> nat := (fun m => n).
Definition fplus (f g: nat -> nat) := fun n => f n + g n.
Definition smult (k : nat) (f : nat -> nat) := fun n => k*f n.

Lemma sum_over_fns : forall i j f g,
  sum i j f + sum i j g = sum i j (fplus f g).
Proof.
  intros.
  remember (nat_compare i j) as C.
  destruct  C. assert (i =j). apply nat_compare_eq_iff. auto. rewrite H. rewrite sum_eq.
  rewrite sum_eq. rewrite sum_eq. unfold fplus. auto.
  assert (i < j). apply nat_compare_lt. auto.
  apply (well_founded_ind lt_wf (fun j => forall i f g, i < j -> sum i j f + sum i j g = sum i j (fplus f g))); auto.
  clear. intros.
  destruct H0.
  repeat (rewrite sum_S_j; try omega). repeat (rewrite sum_eq). unfold fplus. omega.
  repeat (rewrite sum_S_j; try omega).
 rewrite <- H. unfold fplus. omega. auto. auto.
 assert (i > j). apply nat_compare_gt. auto. repeat (rewrite sum_gt; auto).
Qed.

Lemma sum_scalar_prod : forall i j k f, sum i j (smult k f ) = k * sum i j f.
Proof.
  intros.
   remember (nat_compare i j) as C.
  destruct C. assert (i =j). apply nat_compare_eq_iff. auto. rewrite H. rewrite sum_eq. unfold smult.
  rewrite sum_eq. auto.
   assert (i < j). apply nat_compare_lt. auto.
  apply (well_founded_ind lt_wf (fun j => forall i k f, i < j ->sum i j (smult k f) = k * sum i j f )); auto.
  clear. intros.
  destruct H0. repeat (rewrite sum_S_j; try omega). repeat (rewrite sum_eq). 
  unfold smult. rewrite mult_plus_distr_l. auto.
  repeat (rewrite sum_S_j; try omega). 
  rewrite  H; auto. rewrite mult_plus_distr_l. unfold smult. auto.
  assert (i > j). apply nat_compare_gt. auto. repeat (rewrite sum_gt; auto).
Qed.

Lemma split_sum : forall i j k f, i <= j -> j < k -> sum i j f + sum (S j) k f = sum i k f.
Proof.
  intros.
  apply (well_founded_ind lt_wf (fun j => forall i k, i <= j -> j < k -> sum i j f + sum (S j) k f = sum i k f)); auto.
  clear.
  intros.
  destruct x.
  inversion H0.
  repeat (rewrite sum_S_j; try omega). rewrite sum_eq.
  replace (sum 0 k f) with (f 0 + sum 1 k f). auto.
  rewrite <- sum_adds. auto. omega.
  inversion H0. rewrite sum_eq. rewrite <- sum_adds; omega.
  rewrite sum_S_j; try omega.
  rewrite <- plus_assoc.
  replace  (f (S x) + sum (S (S x)) k f) with (sum (S x) k f);[|rewrite sum_adds; omega].
  inversion H0. rewrite sum_gt.
  rewrite plus_0_l. auto.
  auto.
  rewrite H; auto. omega.
 Qed.


Lemma sum_splits_inc :
  forall i j k f,
    i < k -> k < j ->
    sum k j f <= sum i j f.
Proof.
  intros.
  replace (sum i j f) with (sum i (k-1) f + sum (k) j f).
  replace (sum k j f) with (0 + sum k j f);[|omega].
  apply plus_le_compat;auto. inversion H. omega. omega.
  destruct k. inversion H.
  replace (S k - 1) with k;[|omega].
  inversion H.
  rewrite split_sum; auto. omega.
  rewrite split_sum; omega.
Qed.  


Lemma sum_preserves_order :
  forall i j f g, (forall n, i <= n -> f n <= g n) -> sum i j f <= sum i j g.
Proof.
  intros.
  remember (nat_compare i j) as C.
  destruct C.
  assert (i = j);[apply nat_compare_eq_iff; auto|]. subst. repeat (rewrite sum_eq). apply H. auto.  
  assert (i < j). apply nat_compare_lt. auto.
  apply (well_founded_ind lt_wf (fun j => forall i f g, (forall n, i <= n -> f n <= g n) -> i < j ->  sum i j f <= sum i j g)); auto.
  clear.
  intros. destruct x. inversion H1.
  destruct H1. repeat (rewrite sum_S_j ; auto). repeat (rewrite sum_eq).
  apply plus_le_compat; auto. 
  repeat (rewrite sum_S_j; auto). apply plus_le_compat; auto. apply H0. omega.
  assert (j < i);[apply nat_compare_gt; auto|]. repeat (rewrite sum_gt); auto.
Qed.


Lemma sum_preserves_order_in_range :
  forall i j f g, (forall n, i<=n -> n<=j -> f n <= g n) -> sum i j f <= sum i j g.
Proof.
  intros.
  remember (nat_compare i j) as C.
  destruct C.
  assert (i = j);[apply nat_compare_eq_iff; auto|]. subst.
  repeat (rewrite sum_eq). apply H; auto.

  assert (i < j). apply nat_compare_lt. auto.
  apply (well_founded_ind
           lt_wf
           (fun j => forall i f g,
                       (forall n, i <= n -> n <= j -> f n <= g n) ->
                       i < j ->
                       sum i j f <= sum i j g)); auto.
  clear.
  intros.
  destruct x. inversion H1.
  destruct H1. repeat (rewrite sum_S_j ; auto).
  apply plus_le_compat. repeat (rewrite sum_eq). apply H0. auto. auto.
  apply H0. auto. auto.
  repeat (rewrite sum_S_j); try omega.
  apply plus_le_compat.
  apply H; auto. apply H0; try omega.
  assert (j < i);[apply nat_compare_gt; auto|]. repeat (rewrite sum_gt); auto.
Qed.
  
  
  

Theorem sum_is_sumlist_map : forall i j f, sum i j f = sumlist (map f (listfrom i j)).
Proof.
  intros.
  remember (nat_compare i j) as C.
  destruct C.
  assert (i = j). apply nat_compare_eq_iff. auto. rewrite H. rewrite sum_eq. rewrite listfrom_i_i.
  simpl. auto.
  assert (i < j). apply nat_compare_lt. auto. unfold listfrom.
  remember (S j - i) as k.
  apply (well_founded_ind lt_wf
             (fun k => forall i j, i < j -> k= S j - i -> sum i j f = sumlist (map f (listfrom_acc i k)))); auto.
  clear.  intros. induction x. intuition.
  inversion H0.  subst. assert (S x = 2). omega. rewrite H2. simpl.
  assert ((i ?= S i) = Lt). apply nat_compare_lt. auto. rewrite H3. rewrite sum_eq. auto.
  rewrite sum_adds; try omega. rewrite H with (y:= x). simpl. auto. auto. omega. subst. omega.
  assert (j < i). apply nat_compare_gt. auto. rewrite sum_gt; auto. unfold listfrom.
  assert (S j - i = 0). omega. rewrite H0. simpl. auto.
Qed.


Lemma sum_extensionality :
  forall i j f g,
    (forall n, f n = g n) ->
    sum i j f = sum i j g.
Proof.
  intros.
  remember (nat_compare i j) as C.
  destruct C.
  assert (i=j). apply nat_compare_eq_iff. auto.
  rewrite H0. repeat (rewrite sum_eq). apply H.

  assert (i<j). apply nat_compare_lt. auto.
  apply (well_founded_ind lt_wf (fun j => forall i, i < j -> sum i j f = sum i j g)); auto.
  intros.
  destruct x. intuition.
  rewrite sum_S_j; auto.
  rewrite sum_S_j; auto.
  inversion H2. repeat (rewrite sum_eq). auto.
  rewrite H1; auto.    
  assert (i > j). apply nat_compare_gt. auto.
  repeat (rewrite sum_gt); auto.
Qed.
  
  
Theorem function_is_a_sum :
  forall fuel n f g,
    (forall n, f 0 n = 1) ->
    (forall fuel n, f (S fuel) n = g n + f fuel (S n)) ->
    0 < fuel ->
    f fuel n = 1 + sum 0 (fuel - 1) (fun m => g (n+m)).
Proof.
  intros.
  apply (well_founded_ind
           lt_wf
           (fun fuel => forall n, 0 < fuel -> f fuel n = 1 + sum 0 (fuel - 1) (fun m => g (n + m)))); auto.
  intros.
  destruct x. inversion H3.
  destruct x. simpl.
  rewrite H0.  rewrite H. rewrite plus_0_r. omega.
  rewrite H0. rewrite sum_adds.
  replace (S (S x) - 1) with (S x);[|omega].
  rewrite plus_0_r.
  rewrite H2; try omega.
  rewrite sum_shifts.
  unfold shift.
  replace (S x - 1) with x;[|omega].
  assert ((sum 0 x (fun m : nat => g (S n0 + m))) = (sum 0 x (fun n1 : nat => g (n0 + S n1)))).
  apply sum_extensionality.
  intros. replace (S n0 + n1) with (n0 + S n1). auto. omega.
  rewrite H4.  
  omega.
  omega.
Qed.

(* the formulation of shift_by seems to make this harder than it should be *)
Lemma sum_shifts_k :
  forall i j f k, sum i j (shift_by k f) = sum (i+k) (j+k) f.
Proof.
  intros.
  apply (well_founded_ind lt_wf (fun k => forall f,
                                            sum i j (shift_by k f) = sum (i + k) (j + k) f)).
  clear.
  intros.
  destruct x.
  unfold shift_by.
  repeat (rewrite plus_0_r). apply sum_extensionality.
  intros. rewrite plus_0_r. auto.
  replace (i + S x) with (S (i+x));[|omega].
  replace (j + S x) with (S(j+x));[|omega].
  rewrite sum_shifts.
  rewrite <- H; auto.
  apply sum_extensionality.
  intros.
  rewrite shift_by_S.
  unfold shift.
  unfold shift_by. simpl. auto.
Qed.

Lemma monotone_sum :
  forall i j f,
    monotone f ->
    sum i j (const (f i)) <= sum i j f.
Proof.
  intros.
  apply sum_preserves_order.
  intros.
  unfold const.
  apply H. auto.
Qed.