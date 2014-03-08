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

Lemma assoc_helper1:
  forall (A B : Set) (PA : A -> nat -> Prop) (PB : B -> nat -> Prop),
         (forall x : A,
                (exists an : nat, PA x an) ->
                forall x1 : B,
                (exists an : nat,
                   (fun (b : B) (bn : nat) =>
                    forall an0 : nat, PA x an0 -> PB b (an0 + bn)) x1 an) ->
                (fun a : B => exists an : nat, PB a an) x1).
Proof.
  intros A B PA PB a [an pa] b [an' PAB].
  apply PAB in pa.
  eauto.
Defined.

Lemma assoc_helper2:
  forall (A B G : Set) (PA : A -> nat -> Prop) (PB : B -> nat -> Prop) (PG : G -> nat -> Prop),
  forall x : A,
            (exists an : nat, PA x an) ->
            forall x1 : B,
            (exists an : nat,
               (fun (b : B) (bn : nat) =>
                forall an0 : nat, PA x an0 -> PB b (an0 + bn)) x1 an) ->
            (forall g gn anbn,
               PB x1 anbn ->
               PG g (anbn + gn)) ->
            forall x3 : G,
            (exists an : nat, PG x3 an) ->
            (fun a : G =>
             exists an : nat,
               (fun (b : G) (bn : nat) =>
                forall an0 : nat, PA x an0 -> PG b (an0 + bn)) a an) x3.
Proof.
  intros A B G PA PB PG a [an pa] b [bn pb] pbg g [gn pg].
  exists (an + bn).
  intros an' pa'.
  apply pb in pa'.
  replace (an' + (an + bn)) with ((an' + bn) + an); try omega.
  eapply pbg.
  apply pa'.
Qed.

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
    ggp,
    sig_eqv G _ _
            (bind B PB G PG
                  (bind A PA B PB
                        ma
                        fb)
                  gg)
            (bind A PA G PG
                  ma
                  (fun (a:A) (pa:exists an, PA a an) => 
                     let (b, pbe) := (fb a pa) in
                     let mb' := exist _ b (assoc_helper1 A B PA PB a pa b pbe) in
                     let (_, pbe') := mb' in
                     let (g, pge) := bind B PB G PG mb' gg in
                     let mg' := exist _ g (assoc_helper2 A B G PA PB PG a pa b pbe (ggp b) g pge) in
                     mg')).
Proof.
  intros.

  destruct ma as [a [an pa]].
  remember (ex_intro (fun n : nat => PA a n) an pa) as pae.
  simpl.
  remember (assoc_helper1 A B PA PB a pae) as helper1'.
  remember (assoc_helper2 A B G PA PB PG a pae) as helper2'.
  clear Heqhelper1' Heqhelper2'.
  rename helper1' into helper1.
  rename helper2' into helper2.

  remember (fb a pae) as mb.
  rewrite Heqpae.
  destruct mb as [b [bn pb]].
  clear Heqpae pae Heqmb.

  remember (ex_intro (fun an0 : nat => PB b an0) (an + bn) (pb an pa)) as pbe.
  remember (ex_intro
              (fun an0 : nat =>
                 forall an1 : nat, PA a an1 -> PB b (an1 + an0)) bn
              pb) as pbe'.
  simpl.
  remember (helper1 b pbe') as helper1'.
  remember (helper2 b pbe') as helper2'.
  clear helper1 helper2 Heqhelper1' Heqhelper2'.
  simpl in helper1'. rename helper1' into pbe''.

  replace pbe'' with pbe.
  remember (gg b pbe) as mg.
  rewrite Heqpbe.
  destruct mg as [g [gn pg]].

  unfold sig_eqv. simpl. intuition.

  apply proof_irrelevance.
Qed.
