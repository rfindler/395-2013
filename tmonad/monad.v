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

Theorem left_identity_value:
  forall A B PA PAB x PAx yf,
    (proj1_sig (bind A B PA PAB (ret A PA x PAx) yf)) = 
    (proj1_sig (yf x (ex_intro (PA x) 0 PAx))).
Proof.
  intros A B PA PAB x PAx yf.
  unfold bind. unfold ret. simpl.
  remember (yf x (ex_intro (PA x) 0 PAx)) as y.
  destruct y as [y [yn Py]]. simpl in *.
  auto.
Qed.

(* XXX There should be a better way to write this *)
Theorem left_identity_proof:
  forall A B PA PAB x PAx yf,
    (exists n : nat,
       PAB (proj1_sig (ret A PA x PAx)) 
           (proj1_sig (bind A B PA PAB (ret A PA x PAx) yf)) n) <->
    (exists n : nat,
       forall xn : nat,
         PA x xn -> PAB x (proj1_sig (yf x (ex_intro (PA x) 0 PAx))) (xn + n)).
Proof.
  intros A B PA PAB x PAx yf.
  unfold bind. unfold ret. simpl.
  remember (yf x (ex_intro (PA x) 0 PAx)) as y.
  destruct y as [y [yn Py]]. simpl in *.
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

Theorem right_identity_value:
  forall A PA m,
    (proj1_sig (bind A A PA
                     (fun a1 a2 an => PA a1 an) m 
                     (fun a1 pa => 
                        ret A 
                            (fun a2 an => 
                               forall xn : nat, 
                                 PA a1 xn -> 
                                 PA a1 (xn + an))
                            a1
                            (right_identity_helper A PA a1 pa)))) =
    (proj1_sig m).
Proof.
  intros A PA m.
  unfold bind. unfold ret. simpl.
  destruct m as [a [an pa]]. simpl.
  auto.
Qed.

Theorem right_identity_proof:
  forall (A:Set) (PA:A -> nat -> Prop) (m:C A PA),
    (exists n : nat, PA (proj1_sig m) n) <->
    (exists n : nat, PA (proj1_sig m) n).
Proof.
  intuition.
Qed.

Theorem associativity_value:
  forall 
    (A:Set)
    (B:Set)
    (G:Set)
    (PA:A -> nat -> Prop)
    (PB:B -> nat -> Prop)
    (PAB:A -> B -> nat -> Prop)
    (PBG:B -> G -> nat -> Prop)
    (PAG:A -> G -> nat -> Prop)
    (ma:C A PA)
    (fb1:forall (a:A) (pa:exists an, PA a an),
          C B
            (fun b bn =>
                forall an : nat, 
                  PA a an -> 
                  PAB a b (an + bn)))
    (fb2:forall (a:A) (pa:exists an, PA a an),
          C B PB)
    (fb_eq:
       forall a pa,
         proj1_sig (fb1 a pa) = proj1_sig (fb2 a pa))
    (gg1:forall (b:B) (pb:exists bn, PAB (proj1_sig ma) b bn),
          C G
            (fun g gn =>
               forall anbn : nat,
                 PAB (proj1_sig ma) b anbn ->
                 PBG b g (anbn + gn)))
    (gg2:forall (a:A) (b:B) (pb:exists bn, PB b bn),
          C G
            (fun g gn =>
               forall bn : nat,
                 PB b bn ->
                 PBG b g (bn + gn)))
    (gg_eq:
       forall a b pb1 pb2,
         proj1_sig (gg1 b pb1) = proj1_sig (gg2 a b pb2))
    (helper1:forall (a : A) (pa:exists an, PA a an) (g : G)
                    (pag : (exists gn, (PBG (proj1_sig (fb2 a pa)) g gn))),
               (exists gn : nat,
                  forall an : nat, PA a an -> PAG a g (an + gn))),
    (proj1_sig 
       (bind B G (PAB (proj1_sig ma)) PBG
             (bind A B PA PAB
                   ma
                   fb1)
             gg1)) =
    (proj1_sig
       (bind A G PA PAG
             ma 
             (fun (a:A) (pa:exists an, PA a an) => 
                let mg := 
                    (bind B G PB PBG
                          (fb2 a pa)
                          (gg2 a)) in
                (exist _ (proj1_sig mg) (helper1 a _ (proj1_sig mg) (proj2_sig mg)))))).
Proof.
  intros.
  unfold bind.
  simpl.
  destruct ma as [a [an pa]].
  remember (ex_intro (fun n : nat => PA a n) an pa) as pae.
  simpl.
  remember (fb_eq a pae) as fb_eq'.
  clear Heqfb_eq'.
  remember (fb1 a pae) as mb1.
  remember (fb2 a pae) as mb2.
  destruct mb1 as [b1 [bn1 pb1]].
  destruct mb2 as [b2 [bn2 pb2]].
  simpl in *. subst b2.

  remember (ex_intro (fun n : nat => PAB a b1 n) (an + bn1) (pb1 an pa)) as pb1e.
  remember (ex_intro (fun n : nat => PB b1 n) bn2 pb2) as pb2e.
  remember (gg_eq a b1 pb1e pb2e) as gg_eq'.
  clear Heqgg_eq'.
  remember (gg1 b1 pb1e) as mg1.
  remember (gg2 a b1 pb2e) as mg2.

  destruct mg1 as [g1 [gn1 pg1]].
  destruct mg2 as [g2 [gn2 pg2]].
  simpl in *. subst g2.

  auto.
Qed.

Theorem associativity_proof:
  forall 
    (A:Set)
    (B:Set)
    (G:Set)
    (PA:A -> nat -> Prop)
    (PB:B -> nat -> Prop)
    (PAB:A -> B -> nat -> Prop)
    (PBG:B -> G -> nat -> Prop)
    (PAG:A -> G -> nat -> Prop)
    (ma:C A PA)
    (fb1:forall (a:A) (pa:exists an, PA a an),
          C B
            (fun b bn =>
                forall an : nat, 
                  PA a an -> 
                  PAB a b (an + bn)))
    (fb2:forall (a:A) (pa:exists an, PA a an),
          C B PB)
    (fb_eq:
       forall a pa,
         proj1_sig (fb1 a pa) = proj1_sig (fb2 a pa))
    (gg1:forall (b:B) (pb:exists bn, PAB (proj1_sig ma) b bn),
          C G
            (fun g gn =>
               forall anbn : nat,
                 PAB (proj1_sig ma) b anbn ->
                 PBG b g (anbn + gn)))
    (gg2:forall (a:A) (b:B) (pb:exists bn, PB b bn),
          C G
            (fun g gn =>
               forall bn : nat,
                 PB b bn ->
                 PBG b g (bn + gn)))
    (gg_eq:
       forall a b pb1 pb2,
         proj1_sig (gg1 b pb1) = proj1_sig (gg2 a b pb2))
    (helper1:forall (a : A) (pa:exists an, PA a an) (g : G)
                    (pag : (exists gn, (PBG (proj1_sig (fb2 a pa)) g gn))),
               (exists gn : nat,
                  forall an : nat, PA a an -> PAG a g (an + gn))),
    (exists n : nat,
       PBG (proj1_sig (bind A B PA PAB ma fb1))
           (proj1_sig
              (bind B G (PAB (proj1_sig ma)) PBG (bind A B PA PAB ma fb1) gg1)) n)
    <->
    (exists n : nat,
       PAG (proj1_sig ma)
           (proj1_sig
              (bind A G PA PAG ma
                    (fun (a : A) (pa : exists an : nat, PA a an) =>
                       let mg := bind B G PB PBG (fb2 a pa) (gg2 a) in
                       exist
                         (fun a0 : G =>
                            exists n0 : nat,
                              forall xn : nat, PA a xn -> PAG a a0 (xn + n0))
                         (proj1_sig mg) (helper1 a pa (proj1_sig mg) (proj2_sig mg)))))
           n).
Proof.
  intros.
  unfold bind.
  simpl.
  destruct ma as [a [an pa]].
  remember (ex_intro (fun n : nat => PA a n) an pa) as pae.
  simpl.

  remember (helper1 a pae) as helper1'.
  clear Heqhelper1'.
  remember (fb_eq a pae) as fb_eq'.
  clear Heqfb_eq'.
  remember (fb1 a pae) as mb1.
  remember (fb2 a pae) as mb2.
  destruct mb1 as [b1 [bn1 pb1]].
  destruct mb2 as [b2 [bn2 pb2]].
  simpl in *. subst b2.

  remember (ex_intro (fun n : nat => PAB a b1 n) (an + bn1) (pb1 an pa)) as pb1e.
  remember (ex_intro (fun n : nat => PB b1 n) bn2 pb2) as pb2e.
  remember (gg_eq a b1 pb1e pb2e) as gg_eq'.
  clear Heqgg_eq'.
  remember (gg1 b1 pb1e) as mg1.
  remember (gg2 a b1 pb2e) as mg2.

  destruct mg1 as [g1 [gn1 pg1]].
  destruct mg2 as [g2 [gn2 pg2]].
  simpl in *. subst g2.
  
  split; intros [gn pg'].

  edestruct (helper1' g1); eauto.

  eauto.
Qed.
