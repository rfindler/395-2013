Definition C (A:Set) (P:A -> nat -> Prop) : Set := {a | exists n, (P a n)}.
Hint Unfold C.

Definition ret (A:Set) (PA:A -> nat -> Prop) (x:A) (PAx:PA x 0) : C A PA.
Proof.
  exists x.
  exists 0.
  apply PAx.
Defined.

Definition bind (A:Set) (B:Set)
           (PA:A -> nat -> Prop) (PAB:A -> B -> nat -> Prop)
           (xm:C A PA) 
           (yf:forall x (xm:exists n, PA x n),
                 C B 
                   (fun y yn => 
                      forall xn, 
                        PA x xn ->
                        PAB x y (xn+yn)))
: C B (PAB (proj1_sig xm)).
Proof.
  destruct xm as [x Px].
  edestruct (yf x Px) as [y Py].
  exists y.
  destruct Px as [xn Px].
  destruct Py as [yn Py].
  exists (xn + yn).
  eapply Py.
  apply Px.
Defined.

Definition inc (A:Set) PA (x:C A (fun x xn => PA x (xn+1)))
: C A PA.
Proof.
  destruct x as [x Px].
  exists x.
  destruct Px as [n Px].
  exists (n + 1).
  apply Px.
Defined.

Notation "<== x" := (ret _ _ x _) (at level 55).
Notation "++ ; c" := (inc _ _ c) (at level 30, right associativity).
Notation "x <- y ; z" := (bind _ _ _ (fun _ _ => _) y (fun (x : _) (xm : _) => z) ) (at level 30, right associativity).
Notation "x >>= y" := (bind _ _ _ (fun _ _ => _) x y) (at level 55).
Notation "x >> y" := (bind _ _ _ (fun _ => _) x (fun _ => y)) (at level 30, right associativity).

Notation "{! x !:! A !<! c !>!  P !}" := (C A (fun (x:A) (c:nat) => P)) (at level 55).

Definition sig_eqv A (P1:A -> Prop) (P2:A -> Prop) (s1:sig P1) (s2:sig P2) : Prop :=
  let v1 := (proj1_sig s1) in
  let v2 := (proj1_sig s2) in
  v1 = v2 /\ (P1 v1 <-> P2 v2).

Theorem left_identity:
  forall A B PA PAB x PAx yf,
    sig_eqv _ _ _ 
            (bind A B PA PAB (ret A PA x PAx) yf)
            (yf x (ex_intro (PA x) 0 PAx)).
Proof.
  intros A B PA PAB x PAx yf.
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
            (bind A A PA
                     (fun a1 a2 an => PA a1 an) m 
                     (fun a1 pa => 
                        ret A 
                            (fun a2 an => 
                               forall xn : nat, 
                                 PA a1 xn -> 
                                 PA a1 (xn + an))
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
    (PAB:A -> B -> nat -> Prop)
    (PABG:A -> B -> G -> nat -> Prop)
    (ma:C A PA)
    (fb:forall (a:A) (pa:exists an, PA a an),
          C B
            (fun b bn =>
                forall an : nat, 
                  PA a an -> 
                  PAB a b (an + bn)))
    (gg:forall (b:B) (pb:exists bn, PAB (proj1_sig ma) b bn),
          C G
            (fun g gn =>
               forall anbn : nat,
                 PAB (proj1_sig ma) b anbn ->
                 PABG (proj1_sig ma) b g (anbn + gn)))
    helper1 helper2 helper3,
    sig_eqv _ _ _
            (bind B G (PAB (proj1_sig ma)) 
                  (fun b g n => PABG (proj1_sig ma) b g n)
                  (bind A B PA PAB
                        ma
                        fb)
                  gg)
            (bind A G PA
                  (fun a g n => 
                     PABG a 
                          (proj1_sig (fb (proj1_sig ma) (proj2_sig ma)))
                          g n)
                  ma
                  (fun (a:A) (pa:exists an, PA a an) => 
                     let mg :=
                         (bind B G
                               (fun b bn => 
                                  forall an,
                                    PA a an ->
                                    PAB a b (an + bn))
                               (fun b g bngn =>
                                  PABG a b g bngn)
                               (fb a pa)
                               (fun b pb =>
                                  let mg := gg b (helper1 a pa b pb) in
                                  let (g, pg) := mg in
                                  exist _ g (helper2 a pa b pb g pg))) in
                     let (g, pg) := mg in
                     exist _ g (helper3 a pa g pg))).
Proof.
  intros.
  unfold sig_eqv, bind.
  destruct ma as [a [an pa]].
  remember (ex_intro (fun n : nat => PA a n) an pa) as pae.

  simpl in *.

  remember (helper1 a pae) as helper1'.
  remember (helper2 a pae) as helper2'.
  remember (helper3 a pae) as helper3'.
  clear Heqhelper1' helper1 Heqhelper2' helper2 Heqhelper3' helper3.

  remember (fb a pae) as mb.
  destruct mb as [b [bn pb]].
  simpl in *.
  remember (ex_intro (fun n : nat => PAB a b n) (an + bn) (pb an pa)) as pbe1.
  remember (ex_intro
              (fun n : nat =>
                 forall an0 : nat,
                   PA a an0 -> PAB a b (an0 + n)) bn pb) as pbe2.

  replace (helper1' b pbe2) with pbe1 in *.

  remember (gg b pbe1) as mg.
  destruct mg as [g [gn pg]].
  simpl in *.

  intuition.

  apply proof_irrelevance.
Qed.
