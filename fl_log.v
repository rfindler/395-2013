Require Import Arith Arith.Even Arith.Div2 Omega.
Require Import Coq.Logic.JMeq Coq.Program.Wf.
Require Import Program.Syntax.
Require Import util.

Set Implicit Arguments.

Section fl_log.

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

  Lemma fl_log_div2' : forall n, fl_log (S n) = S (fl_log (div2 n)).
    intros.
    apply (Fix_eq _ lt lt_wf (fun _ => nat)).
    intuition.
    destruct x; [ reflexivity | repeat f_equal].
  Qed.

  Lemma fl_log_div2 : forall n, fl_log (div2 n) + 1 = fl_log (S n).
    intros n.
    rewrite fl_log_div2'.
    intuition.
  Qed.

  Lemma double_div2 : forall n, div2 (n + n) = n.
    induction n.
    compute; reflexivity.
    replace (S n + S n) with (S (S (n + n))); [|omega].
    unfold div2; fold div2.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma odd_div2 : (forall n, div2 (S (n + n)) = n).
    induction n.
    compute; reflexivity.
    replace (S (S n + S n)) with (S (S (S n + n))) ; [|omega].
    unfold div2 at 1.
    fold div2.
    replace (S n + n) with (S (n + n)) ; [|omega].
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma fl_log_odd :
    forall n : nat, fl_log (n + n + 1) = (fl_log n) + 1.
    intro n.
    rewrite plus_comm; simpl.
    rewrite fl_log_div2'.
    rewrite double_div2.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

  Lemma fl_log_even :
    forall n : nat, fl_log ((n + 1) + (n + 1)) = (fl_log n) + 1.
    intro n.
    replace (n + 1 + (n + 1)) with (S (S (n + n))) ; [|omega].
    rewrite fl_log_div2'.
    rewrite odd_div2.
    rewrite plus_comm; simpl; reflexivity.
  Qed.

End fl_log.
