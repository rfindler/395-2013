Require Import Braun.tmonad.monad.
Require Import Braun.common.braun.

Section size_linear.
  Variable A : Set.
  Locate "{ _ : _ | _ }".

  (* If it's a braun tree, this is its size *)
  Definition ifBraunSize (bt : @bin_tree A) n : Prop :=
    forall (p : (sig (fun m : nat => Braun bt m))), proj1_sig p = n.
  
  Program Fixpoint size_linear (bt : @bin_tree A) : { n !:! nat !<! c !>!
                                                        n = c /\ ifBraunSize bt n
                                                    } :=
    match bt with
      | bt_mt =>
        <== 0
      | bt_node x l r =>
        ++ ;
          lsize <- size_linear l;
          rsize <- size_linear r;
          <== lsize + rsize + 1
    end.
  Next Obligation.
  Proof.
    split; [auto |].
    unfold ifBraunSize.
    intros.
    remember (proj2_sig p) as P.
    inversion P.
    auto.
  Qed.
  Next Obligation.
    split; [omega|].
    unfold ifBraunSize.
    unfold ifBraunSize in H1, H2.
    intros.
    remember (proj2_sig p) as BT.
    simpl in BT; inversion BT; subst.
    assert (s_size = xn0); [| assert (t_size = xn)].
    remember (H1 (exist (Braun l) s_size H6)); auto.
    remember (H2 (exist (Braun r) t_size H7)); auto.
    auto.
  Qed.
End size_linear.
