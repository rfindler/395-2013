Require Import Program Omega List.
Require Import Braun.common.util Braun.monad.smonad.

(* this is the working definition of enq; *)
(*   commented out because it doesn't work yet *)

Program Definition enq (addr : nat) (n : nat) :
  (CS ()
      (fun st => True)
      (fun _ st st' k =>
         k = 11 /\
         ((fst st') addr)
         =
         (cons n (fst ((fst st) addr)),
          (snd ((fst st) addr))))) :=
                          
  q <- get addr;
  addr ::== (cons n (fst q), snd q);
  (* += 11; *)
  <== ().

Next Obligation.
 rename x into st0.
 rename x0 into PRE.
 unfold proj1_sig. 
 remember  (q <- !addr; addr ::== (n :: fst q, snd q); (<== ())) as P. 
 unfold CS in *.
 edestruct (P st0 PRE) as [ [t st1] Q ].
 clear P HeqP PRE.
 destruct Q as [an [a [st2 [bn [cn [[EQ1 [EQ2 EQ3]] Q]]]]]].
 subst a bn st2.
 destruct Q as [[_ [st2 [dn [en Q]]]] EQ1].
 destruct Q as [Q [P EQ2]].
 destruct P as [EQ3 [EQ4 EQ5]].
 subst en cn an t st2.
 destruct Q as [EQ1 [EQ2 [EQ3 Q]]].
 subst dn.
 destruct st0 as [st0_m st0_n].
 destruct st1 as [st1_m st1_n].
 simpl in *. subst st1_n.
 exists 11.
 split. auto.
 rewrite EQ3. auto.
Qed.

(* old definitions:

Definition enq : nat -> nat -> S () := 
  fun addr n => 
    bind (get addr)
         (fun q =>
           match q with
             | (front,back) => set addr (cons n front,back)
           end).

Definition deq : nat -> S (option nat) :=
  fun addr =>
    bind (get addr)
         (fun q => 
            match q with
              | (nil,nil) => ret None
              | (front,cons back more) => 
                bind (set addr (front,more))
                     (fun _ => ret (Some back))
              | (cons front more, nil) =>
                match rev' (cons front more) with
                  | nil => ret None (* can't happen *)
                  | (cons back more') =>
                    bind (set addr (nil,more'))
                         (fun _ => ret (Some back))
                end 
            end).

Example ex1 : run (bind alloc (fun addr => (bind (enq addr 1) (fun _ => (deq addr)))))
              = run (ret (Some 1)).
Proof.
  compute.
  reflexivity.
Qed.

Example ex2 : run (bind alloc
                        (fun addr =>
                           bind (enq addr 1) 
                                (fun _ =>
                                   bind (enq addr 2)
                                        (fun _ =>
                                           bind (deq addr)
                                                (fun _ => (deq addr))))))
              = run (ret (Some 2)).
Proof.
  compute.
  reflexivity.
Qed.

Theorem enq_correct : 
  forall l1 l2 n addr,
    run_s (bind (set addr (l1,l2))
                (fun _ => (enq addr n)))
          [addr]
         = ((), [l2 ++ rev' l1 ++ [n]]).
Proof.
  unfold enq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  intros l1 l2 n addr.
  simpl.
  dispatch_if X X';[clear X|intuition].
  dispatch_if X X';[clear X|intuition].
  replace (rev' (n::l1)) with (rev (n::l1));
    [| unfold rev' ; rewrite rev_alt; auto].
  simpl.
  replace (rev l1) with (rev' l1);
    [| unfold rev' ; rewrite rev_alt; auto].
  auto.
Qed.

Lemma nonempty_rev_nonempty : forall (x:nat) xs, [] = rev' (x :: xs) -> False.
  intros x xs BAD.
  unfold rev' in BAD.
  rewrite <- rev_alt in BAD.
  assert (length (nil:list nat) = length (rev (x :: xs))) as BAD_LEN;
    [rewrite BAD;reflexivity|clear BAD].
  rewrite rev_length in BAD_LEN.
  simpl in BAD_LEN.
  intuition.
Qed.

Theorem deq_correct : 
  forall l1 l2 addr,
    run_s (bind (set addr (l1,l2))
                (fun _ => deq addr))
          [addr]
    = match (l2 ++ rev' l1) with
        | [] => (None, [nil])
        | (x :: xs) => (Some x, [xs])
      end.
Proof.
  intros l1 l2 addr.
  remember (app l1 (rev' l2)) as STATE.
  destruct STATE.

  (* queue is empty *)
  symmetry in HeqSTATE.
  apply app_eq_nil in HeqSTATE.
  destruct HeqSTATE.
  subst l1.
  assert (l2 = []).
  destruct l2.
  reflexivity.
  assert False;[|intuition]. 
  apply (nonempty_rev_nonempty n l2).
  auto.
  subst l2.
  compute.
  dispatch_if X X';[clear X | intuition].
  dispatch_if X X';[clear X | intuition].
  auto.

  (* queue nonempty *)

  destruct l2.

  destruct l1.
  simpl.
  compute.
  dispatch_if X X';[clear X | intuition].
  dispatch_if X X';[clear X | intuition].
  auto.

  (* back of queue is empty *)
  unfold deq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  simpl.
  dispatch_if X X';[clear X|intuition].

  remember (rev' (n0::l1)) as LST.
  destruct LST.
  assert False;[|intuition].
  apply (nonempty_rev_nonempty n0 l1).
  auto.

  dispatch_if X X';[clear X|intuition].

  unfold rev'.
  simpl.
  rewrite app_nil_r.
  reflexivity.

  (* back of queue isn't empty *)
  unfold deq.
  unfold bind.
  unfold set.
  unfold get.
  unfold ret.
  unfold run_s.
  simpl.

  dispatch_if X X';[clear X|intuition].

  destruct l1; (dispatch_if X X';[clear X|intuition]); auto.
Qed.

*)
