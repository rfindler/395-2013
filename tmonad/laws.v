Require Import Braun.tmonad.monad.

Definition sig_eqv A (P1:A -> Prop) (P2:A -> Prop) (s1:sig P1) (s2:sig P2) : Prop :=
  let v1 := (proj1_sig s1) in
  let v2 := (proj1_sig s2) in
  v1 = v2 /\ (P1 v1 <-> P2 v2).

Theorem left_identity:
  forall A B PA PB x PAx yf,
    sig_eqv _ _ _ 
            (bind A PA B PB (ret A PA x PAx) yf)
            (yf x (ex_intro (PA x) 0 PAx)).
Proof.
  intros A B PA PB x PAx yf.
  unfold sig_eqv. unfold bind. unfold ret. simpl.
  remember (yf x (ex_intro (PA x) 0 PAx)) as y.
  destruct y as [y [yn Py]]. simpl in *.
  split. auto.
  split.

  intros. exists yn. auto.

  intros [bn BIND]. exists (0 + bn). auto.
Qed.

Require Import Omega.

Lemma right_identity_helper:
  forall (A:Set) (PA:A -> nat -> Prop) (a:A),
    (exists n, PA a n) ->
    (forall xn, PA a xn -> PA a (xn + 0)).
Proof.
  intros A PA x.
  intros [n PAx].
  intros xn H.
  replace (xn + 0) with xn; try omega.
  auto.
Qed.

Theorem right_identity:
  forall A PA m,
    sig_eqv _ _ _
            (bind A PA A PA m 
                     (fun a1 pa => 
                        ret A 
                            (fun a2 an => 
                               forall xn : nat, 
                                 PA a1 xn -> 
                                 PA a2 (xn + an))
                            a1
                            (right_identity_helper A PA a1 pa)))
            m.
Proof.
  intros A PA m.
  unfold sig_eqv, bind, ret. simpl.
  destruct m as [a [an pa]]. simpl.
  intuition.
Qed.

Require Import ProofIrrelevance.

Theorem associativity:
  forall 
    (A:Set)
    (B:Set)
    (G:Set)
    (PA:A -> nat -> Prop)
    (PB:B -> nat -> Prop)
    (PG:G -> nat -> Prop)
    (ma:C A PA)
    (fb:forall (a:A) (pa:exists an, PA a an),
          C B
            (fun b bn =>
                forall an : nat, 
                  PA a an -> 
                  PB b (an + bn)))
    (gg:forall (b:B) (pb:exists bn, PB b bn),
          C G
            (fun g gn =>
               forall anbn : nat,
                 PB b anbn ->
                 PG g (anbn + gn)))
    helper1 helper2,
    sig_eqv _ _ _
            (bind B PB G PG
                  (bind A PA B PB
                        ma
                        fb)
                  gg)
            (bind A PA G PG
                  ma
                  (fun (a:A) (pa:exists an, PA a an) => 
                     let mb := (helper1 a pa (fb a pa)) in
                     helper2 a pa mb (bind B PB G PG mb gg))).
Proof.
  intros.
  unfold sig_eqv, bind.
  destruct ma as [a [an pa]].
  remember (ex_intro (fun n : nat => PA a n) an pa) as pae.

  simpl in *.

  remember (helper1 a pae) as helper1'.
  remember (helper2 a pae) as helper2'.
  clear Heqhelper1' helper1 Heqhelper2' helper2.

  remember (fb a pae) as mb.
  destruct mb as [b [bn pb]].
  simpl in *.

  remember (ex_intro (PB b) (an + bn) (pb an pa)) as pbe1.
  remember (exist
              (fun a0 : B =>
                 exists an0 : nat,
                   forall an1 : nat, PA a an1 -> PB a0 (an1 + an0)) b
              (ex_intro
                 (fun an0 : nat =>
                    forall an1 : nat, PA a an1 -> PB b (an1 + an0)) bn pb))
    as pbe2.
Admitted.

(*

  replace (helper1' pbe2) with (b, pbe1).

  remember (gg b pbe1) as mg.
  destruct mg as [g [gn pg]].
  simpl in *.

  remember (exist
              (fun a0 : B =>
                 exists an0 : nat,
                   forall an1 : nat, PA a an1 -> PB a0 (an1 + an0)) b
              (ex_intro
                 (fun an0 : nat =>
                    forall an1 : nat, PA a an1 -> PB b (an1 + an0)) bn
                 pb))
    as pbe2.
  destruct (helper1' pbe2) as [b' [bn' pb']]. simpl in *.
  remember (ex_intro (fun an0 : nat => PB b' an0) bn' pb')
    as pbe3.
  remember (gg b' pbe3) as mg'.
  destruct mg' as [g' [gn' pg']].
  simpl in *.

*)
