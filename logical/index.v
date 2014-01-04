Require Import Braun.logical.braun Braun.logical.log Braun.logical.util.
Require Import Arith Arith.Even Arith.Div2 List.
Require Import Program.
Require Import Omega.

Inductive IndexR {A:Set} : (@bin_tree A) -> nat -> A -> Prop :=
| IR_zero :
    forall x s t,
      IndexR (bt_node x s t) 0 x
| IR_left :
    forall x s t i y,
      IndexR s i y ->
      IndexR (bt_node x s t) (2 * i + 1) y
| IR_right :
    forall x s t i y,
      IndexR t i y ->
      IndexR (bt_node x s t) (2 * i + 2) y.
Hint Constructors IndexR.

Theorem index_dec :
  forall A (bt:@bin_tree A) i,
    { x | IndexR bt i x } +
    { forall x, ~ IndexR bt i x }.
Proof.
  intros A bt.
  induction bt as [|x s IRs t IRt]; intros i.

  right. intros x IR.
  inversion IR.

  destruct i as [|i].
  left. eauto.

  destruct (even_odd_dec i) as [E | O].

  apply even_2n in E.
  destruct E as [k EQ]. subst.
  unfold double.
  replace (S (k + k)) with (2 * k + 1); try omega.
  destruct (IRs k) as [[y IRs_k] | FAIL].
  left. eauto.
  right. intros y IR.
  inversion IR; clear IR; subst; try omega.
  replace i with k in *; try omega.
  apply (FAIL y); auto.

  apply odd_S2n in O.
  destruct O as [k EQ]. subst.
  unfold double.
  replace (S (S (k + k))) with (2 * k + 2); try omega.
  destruct (IRt k) as [[y IRt_k] | FAIL].
  left. eauto.
  right. intros y IR.
  inversion IR; clear IR; subst; try omega.
  replace i with k in *; try omega.
  apply (FAIL y); auto.
Defined.

Theorem index_Braun :
  forall A (bt:@bin_tree A) n,
    Braun bt n ->
    forall i,
      i < n ->
      exists x,
        IndexR bt i x.
Proof.
  induction bt as [|x s Is t It];
  intros n B i LT.

  inversion B. omega.

  inversion B; clear B; subst.
  rename H2 into BP.
  rename H4 into Bs.
  rename H5 into Bt.
  destruct i as [|i].
  eauto.
  destruct (even_odd_dec i) as [E | O].

  apply even_2n in E. destruct E as [k EQ]; subst.
  unfold double in *.
  destruct (Is s_size Bs k) as [y IRs]; try omega.
  replace (S (k + k)) with (2 * k + 1); try omega.
  eauto.

  apply odd_S2n in O. destruct O as [k EQ]; subst.
  unfold double in *.
  destruct (It t_size Bt k) as [y IRt]; try omega.
  replace (S (S (k + k))) with (2 * k + 2); try omega.
  eauto.
Qed.

Theorem index :
  forall A (bt:@bin_tree A) n,
    Braun bt n ->
    forall i,
      i < n ->
      { x | IndexR bt i x }.
Proof.
  intros A bt n B i LT.
  destruct (index_dec A bt i) as [OK | FAIL].
  auto.
  assert False; try tauto.
  destruct (index_Braun A bt n B i LT) as [y IR].
  apply (FAIL y). auto.
Defined.
