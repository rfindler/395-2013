Require Import Program.

Section monad.
Variable ST : Set.

Definition CS_Pre : Type
  := ST -> Prop.
Definition CS_Post (A:Set) : Type :=
  ST -> A -> nat -> ST -> Prop.

Program Definition
  CS (pre : CS_Pre) (A : Set) (post : CS_Post A) : Set :=
  forall st : { st : ST | pre st },
    { (a, st') : A * ST | exists an, post st a an st' }.
Hint Unfold CS.

Definition top : CS_Pre := fun st => True.

Program Definition ret (A : Set) (post : CS_Post A) 
  : forall av,
    (forall st, post st av 0 st) ->
    CS top A (fun st ap an st' => st = st' /\ ap = av /\ post st ap an st').
Proof.
  intros A post av CPav0.
  unfold CS.
  intros [st pre_st].
  exists (av, st).
  eauto.
Defined.

Program Definition bind:
  forall (A:Set)
    (preA : CS_Pre) (postA : CS_Post A) (am:(CS preA A postA))
    (B:Set) (preB : A -> CS_Pre) (postB : A -> CS_Post B)
    (bf:(forall (a : A)
      (posta:exists st0 an stA,
        postA st0 a an stA),
      (CS (preB a) B
        (fun stA b bn stB =>
          forall st0 an,
            postA st0 a an stA ->
            postB a stA b (an+bn) stB)))),
    CS (fun st0 =>
      preA st0 /\
      (forall a an stA,
        postA st0 a an stA ->
        preB a stA))
    B
    (fun st0 b bn stB =>
      exists a an stA,
        postA st0 a an stA /\
        postB a stA b bn stB).
Proof.
  intros.
  intros [st0 [preA_st0 postApreB]].
  edestruct (am (exist preA st0 preA_st0))
   as [[av stA] postA_stA].
  simpl in postA_stA.
  assert (preB av stA) as preB_stA.
  destruct postA_stA. eauto. simpl.
  assert (exists (st0 : ST) (an : nat) (stA : ST), postA st0 av an stA) as postav.
  destruct postA_stA. exists st0. exists x. exists stA. auto.
  edestruct (bf av postav (exist (preB av) stA preB_stA)) as
    [[bv stB] postApostB_stB].
  simpl in postApostB_stB.
  exists (bv, stB).
  simpl.
  destruct postA_stA as [an postA_stA].
  destruct postApostB_stB as [bn postApostB_stB].
  exists (an + bn). exists av. exists an. eauto. 
Defined.

Program Definition get:
  CS top ST (fun st0 st1 gn st2 => st0 = st1 /\ gn = 0 /\ st2 = st0).
Proof.
  intros [st0 pre_st0].
  exists (st0, st0). simpl.
  eauto.
Defined.

Program Definition put (st2:ST) :
  CS top () (fun _ _ pn st2' => pn = 0 /\ st2 = st2').
Proof.
  intros st2 [st0 pre_st0].
  exists ((), st2).
  eauto.
Defined.

Program Definition inc (k:nat) :
  forall (pre : CS_Pre) (A:Set) (post : CS_Post A),
    CS pre A 
    (fun st a an st' =>
      forall am,
        an + k = am ->
        post st a am st') ->
    CS pre A post.
Proof.
  intros. rename H into am.
  intros [st0 pre_st0]. simpl.
  edestruct (am (exist pre st0 pre_st0))
   as [[av stA] post_stA].
  simpl in *.
  exists (av, stA).
  destruct post_stA as [an post_stA].
  exists (an + k). eauto.
Defined.

End monad.
    
(* xxx example inline for testing *)
Section dumb_list.

  Require Import Omega.
  
Definition ST := list nat.

Program Fixpoint bare_list_insert x (l:list nat) : list nat :=
  match l with
    | nil =>
      (cons x nil)
    | cons y sl =>
      (cons y (bare_list_insert x sl))
  end.

Program Fixpoint list_insert x (l:list nat) :
  (@CS ST (fun st => True) (list nat)
    (fun st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st))
  :=
  match l with
    | nil =>
      (@ret ST (list nat)
        (fun st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st)
        (cons x nil) _)
    | cons y sl =>
      (@bind ST (list nat)
        (fun st => True)
        (fun st r ln st' => r = bare_list_insert x sl /\ ln = length sl /\ st' = st)
        (list_insert x sl)
        (list nat)
        (fun sl' st => sl' = bare_list_insert x sl)
        (fun sl' st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st)
        (fun sl' postsl' =>
          (@inc ST 1 (fun st => True) (list nat)
            (fun st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st)
            (@ret ST (list nat)
              (fun st r ln st' => r = bare_list_insert x l /\ ln = 0 /\ st' = st)
              (cons y sl') _))))
  end.

Next Obligation.
  simpl. eauto.
Defined.

Next Obligation.
  simpl.
  rename x0 into st.
  rename H1 into Pre_st.
  exists (length sl). intros.
  split. auto. split. omega. auto.
Defined.

Next Obligation.
  simpl.
  rename x0 into st.
  rename H4 into Pre_st.
  exists 1.
  intros st0 an [EQr [EQln EQst]].
  split. auto. split. omega. auto.
Defined.

Next Obligation.
  intuition.
Defined.

Next Obligation.
  simpl.
  rename x0 into st.
  rename H into ST_Pre_st.
  destruct (list_insert x sl (exist (fun _ : ST => True) st I)) as [[sl' st'] IH].
  destruct IH as [sl'n [EQsl' [EQsl'n EQst]]].
  simpl in *.
  subst st' sl' sl'n.
  eauto.
Defined.

Program Definition insert (x:nat) :
  @CS ST
  (fun st => True)
  ()
  (fun st _ n st' => n = length st /\ st' = bare_list_insert x st)
  :=
  @bind ST

  ST
  (fun st => True)
  (fun st v vn st' => v = st /\ vn = 0 /\ st' = st)
  (@get ST)

  ()
  (fun av st => st = av)
  (fun av st _ bn st' =>
    st = av /\ bn = length st /\ st' = bare_list_insert x st)
  (fun l postl =>
    (@bind ST

      ST 
      (fun st => st = l)
      (fun st l' l'n st' =>
        l' = bare_list_insert x st /\ l'n = length st /\ st' = st)
      (list_insert x l)
      
      ()
      (fun l' st => l' = bare_list_insert x st)
      (fun l' st _ bn st' =>
        l' = bare_list_insert x st /\ bn = length st /\ st' = l')
      (fun l' postl' =>
        (@put ST l')))).

Next Obligation.
  simpl. eauto.
Defined.

Next Obligation.
  destruct (list_insert x postl (exist (fun _ : ST => True) postl I))
    as [[a st'] [an [EQa [EQan EQst']]]].
  simpl in *.
  eauto.
Defined.

Next Obligation.
  unfold top. auto.
Defined.

Next Obligation.
  eexists. intros st0 an.
  intros [EQr [EQan EQst]].
  subst an x0. eauto.
Defined.

Next Obligation.
  split; auto.
  intros a an stA [EQa [EQan EQst]].
  subst a an stA.
  auto.
Defined.

(* XXX This "proof" is insane. What does it mean? *)
Next Obligation.
  program_simpl.
  edestruct (list_insert x postl _).
  
  destruct (insert_obligation_6 x postl
           (ex_intro
              (fun st0 : ST =>
               exists (an : nat) (stA : ST),
                 postl = st0 /\ an = 0 /\ stA = st0) postl
              (ex_intro
                 (fun an : nat =>
                  exists stA : ST, postl = postl /\ an = 0 /\ stA = postl) 0
                 (ex_intro
                    (fun stA : ST => postl = postl /\ 0 = 0 /\ stA = postl)
                    postl (conj eq_refl (conj eq_refl eq_refl)))))
           (exist (fun st : ST => st = postl) postl eq_refl)).
  simpl in *.
  remember (insert_obligation_3 x postl
             (ex_intro
                (fun st0 : ST =>
                 exists (an : nat) (stA : ST),
                   postl = st0 /\ an = 0 /\ stA = st0) postl
                (ex_intro
                   (fun an : nat =>
                    exists stA : ST, postl = postl /\ an = 0 /\ stA = postl)
                   0
                   (ex_intro
                      (fun stA : ST => postl = postl /\ 0 = 0 /\ stA = postl)
                      postl (conj eq_refl (conj eq_refl eq_refl)))))
             (exist (fun st : ST => st = postl) postl e)).
  simpl in *.
  clear Heqy.
  destruct (list_insert x postl (exist (fun _ : ST => True) postl I)).
  simpl in *.
  destruct x0 as [a st]. simpl in *.
  exists (length postl).
  intros st0 an [EQp [EQan EQp2]].
  subst.
  repeat split; eauto.
  destruct y. intuition.
Qed.

Next Obligation.
  intuition. subst. auto.
Qed.

Next Obligation.
  rename x0 into st0.
  rename H into preA.
  destruct (insert_obligation_8 x (exist (fun _ : ST => True) st0 preA))
    as [preA_st0 postApreB].
  simpl in *.
  clear preA.
  destruct (insert_obligation_1 x (exist (fun _ : ST => True) st0 preA_st0))
    as [an postA_stA].
  simpl in *.
  clear preA_st0.
  destruct postA_stA as [E0 [E1 E2]].
  subst an.
  
  clear postApreB.
  
  
  remember (insert_obligation_7 x x0
             match
               insert_obligation_1 x (exist (fun _ : ST => True) x0 preA_st0)
             with
             | ex_intro x1 H0 =>
                 ex_intro
                   (fun st0 : ST =>
                    exists (an : nat) (stA : ST),
                      x0 = st0 /\ an = 0 /\ stA = st0) x0
                   (ex_intro
                      (fun an : nat =>
                       exists stA : ST, x0 = x0 /\ an = 0 /\ stA = x0) x1
                      (ex_intro
                         (fun stA : ST => x0 = x0 /\ x1 = 0 /\ stA = x0) x0
                         H0))
             end
             (exist (fun st : ST => st = x0) x0
                match
                  insert_obligation_1 x
                    (exist (fun _ : ST => True) x0 preA_st0)
                with
                | ex_intro x1 H0 => postApreB x0 x1 x0 H0
                end)).
  simpl in *.
  rewrite <- Heqy.
  clear Heqy.

  
  destruct ((let (bv, stB) as p
             return
               ((let (_, st') := p in
                 exists an : nat,
                   forall (st0 : ST) (an0 : nat),
                   x0 = st0 /\ an0 = 0 /\ x0 = st0 ->
                   x0 = x0 /\
                   an0 + an = length x0 /\ st' = bare_list_insert x x0) ->
                { (_, st') : () * ST |
                exists (an : nat) (a0 : ST) (an0 : nat) 
                (stA : ST),
                  (a0 = x0 /\ an0 = 0 /\ stA = x0) /\
                  stA = a0 /\ an = length stA /\ st' = bare_list_insert x stA}) :=
             `
             match
               insert_obligation_6 x x0
                 match
                   insert_obligation_1 x
                     (exist (fun _ : ST => True) x0 preA_st0)
                 with
                 | ex_intro x1 H0 =>
                     ex_intro
                       (fun st0 : ST =>
                        exists (an : nat) (stA : ST),
                          x0 = st0 /\ an = 0 /\ stA = st0) x0
                       (ex_intro
                          (fun an : nat =>
                           exists stA : ST, x0 = x0 /\ an = 0 /\ stA = x0) x1
                          (ex_intro
                             (fun stA : ST => x0 = x0 /\ x1 = 0 /\ stA = x0)
                             x0 H0))
                 end
                 (exist (fun st : ST => st = x0) x0
                    match
                      insert_obligation_1 x
                        (exist (fun _ : ST => True) x0 preA_st0)
                    with
                    | ex_intro x1 H0 => postApreB x0 x1 x0 H0
                    end)
             with
             | conj preA_st1 postApreB0 =>
                 (let (av, stA) as p
                      return
                        ((let (a, st') := p in
                          exists an : nat,
                            a = bare_list_insert x x0 /\
                            an = length x0 /\ st' = x0) ->
                         { (_, st') : () * ST |
                         exists (an : nat) (a0 : ST) 
                         (an0 : nat) (stA : ST),
                           (a0 = bare_list_insert x x0 /\
                            an0 = length x0 /\ stA = x0) /\
                           a0 = bare_list_insert x stA /\
                           an = length stA /\ st' = a0}) :=
                      `
                      (list_insert x x0
                         (exist (fun _ : ST => True) x0
                            (insert_obligation_2 x x0
                               match
                                 insert_obligation_1 x
                                   (exist (fun _ : ST => True) x0 preA_st0)
                               with
                               | ex_intro x1 H0 =>
                                   ex_intro
                                     (fun st0 : ST =>
                                      exists (an : nat) 
                                      (stA : ST),
                                        x0 = st0 /\ an = 0 /\ stA = st0) x0
                                     (ex_intro
                                        (fun an : nat =>
                                         exists stA : ST,
                                           x0 = x0 /\ an = 0 /\ stA = x0) x1
                                        (ex_intro
                                           (fun stA : ST =>
                                            x0 = x0 /\ x1 = 0 /\ stA = x0) x0
                                           H0))
                               end
                               (exist (fun st : ST => st = x0) x0 preA_st1)))) in
                  fun
                    postA_stA : exists an : nat,
                                  av = bare_list_insert x x0 /\
                                  an = length x0 /\ stA = x0 =>
                  exist
                    (fun anonymous : () * ST =>
                     let (_, st') := anonymous in
                     exists (an : nat) (a0 : ST) (an0 : nat) 
                     (stA0 : ST),
                       (a0 = bare_list_insert x x0 /\
                        an0 = length x0 /\ stA0 = x0) /\
                       a0 = bare_list_insert x stA0 /\
                       an = length stA0 /\ st' = a0) 
                    ((), av)
                    match postA_stA with
                    | ex_intro an postA_stA0 =>
                        match
                          insert_obligation_5 x x0
                            match
                              insert_obligation_1 x
                                (exist (fun _ : ST => True) x0 preA_st0)
                            with
                            | ex_intro x1 H0 =>
                                ex_intro
                                  (fun st0 : ST =>
                                   exists (an0 : nat) 
                                   (stA0 : ST),
                                     x0 = st0 /\ an0 = 0 /\ stA0 = st0) x0
                                  (ex_intro
                                     (fun an0 : nat =>
                                      exists stA0 : ST,
                                        x0 = x0 /\ an0 = 0 /\ stA0 = x0) x1
                                     (ex_intro
                                        (fun stA0 : ST =>
                                         x0 = x0 /\ x1 = 0 /\ stA0 = x0) x0
                                        H0))
                            end av
                            match postA_stA with
                            | ex_intro x1 H0 =>
                                ex_intro
                                  (fun st0 : ST =>
                                   exists (an0 : nat) 
                                   (stA0 : ST),
                                     av = bare_list_insert x st0 /\
                                     an0 = length st0 /\ stA0 = st0) x0
                                  (ex_intro
                                     (fun an0 : nat =>
                                      exists stA0 : ST,
                                        av = bare_list_insert x x0 /\
                                        an0 = length x0 /\ stA0 = x0) x1
                                     (ex_intro
                                        (fun stA0 : ST =>
                                         av = bare_list_insert x x0 /\
                                         x1 = length x0 /\ stA0 = x0) stA H0))
                            end
                            (exist
                               (fun st : ST => av = bare_list_insert x st)
                               stA
                               match postA_stA with
                               | ex_intro x1 H0 => postApreB0 av x1 stA H0
                               end)
                        with
                        | ex_intro bn postApostB_stB =>
                            ex_intro
                              (fun an0 : nat =>
                               exists (a : ST) (an1 : nat) 
                               (stA0 : ST),
                                 (a = bare_list_insert x x0 /\
                                  an1 = length x0 /\ stA0 = x0) /\
                                 a = bare_list_insert x stA0 /\
                                 an0 = length stA0 /\ av = a) 
                              (an + bn)
                              (ex_intro
                                 (fun a : ST =>
                                  exists (an0 : nat) 
                                  (stA0 : ST),
                                    (a = bare_list_insert x x0 /\
                                     an0 = length x0 /\ stA0 = x0) /\
                                    a = bare_list_insert x stA0 /\
                                    an + bn = length stA0 /\ av = a) av
                                 (ex_intro
                                    (fun an0 : nat =>
                                     exists stA0 : ST,
                                       (av = bare_list_insert x x0 /\
                                        an0 = length x0 /\ stA0 = x0) /\
                                       av = bare_list_insert x stA0 /\
                                       an + bn = length stA0 /\ av = av) an
                                    (ex_intro
                                       (fun stA0 : ST =>
                                        (av = bare_list_insert x x0 /\
                                         an = length x0 /\ stA0 = x0) /\
                                        av = bare_list_insert x stA0 /\
                                        an + bn = length stA0 /\ av = av) stA
                                       (conj postA_stA0
                                          (postApostB_stB x0 an postA_stA0)))))
                        end
                    end)
                   (insert_obligation_3 x x0
                      match
                        insert_obligation_1 x
                          (exist (fun _ : ST => True) x0 preA_st0)
                      with
                      | ex_intro x1 H0 =>
                          ex_intro
                            (fun st0 : ST =>
                             exists (an : nat) (stA : ST),
                               x0 = st0 /\ an = 0 /\ stA = st0) x0
                            (ex_intro
                               (fun an : nat =>
                                exists stA : ST,
                                  x0 = x0 /\ an = 0 /\ stA = x0) x1
                               (ex_intro
                                  (fun stA : ST =>
                                   x0 = x0 /\ x1 = 0 /\ stA = x0) x0 H0))
                      end (exist (fun st : ST => st = x0) x0 preA_st1))
             end in
         fun
           postApostB_stB : exists an : nat,
                              forall (st0 : ST) (an0 : nat),
                              x0 = st0 /\ an0 = 0 /\ x0 = st0 ->
                              x0 = x0 /\
                              an0 + an = length x0 /\
                              stB = bare_list_insert x x0 =>
         exist
           (fun anonymous : () * ST =>
            let (_, st') := anonymous in
            exists (an : nat) (a0 : ST) (an0 : nat) 
            (stA : ST),
              (a0 = x0 /\ an0 = 0 /\ stA = x0) /\
              stA = a0 /\ an = length stA /\ st' = bare_list_insert x stA)
           (bv, stB)
           match
             insert_obligation_1 x (exist (fun _ : ST => True) x0 preA_st0)
           with
           | ex_intro an postA_stA =>
               match postApostB_stB with
               | ex_intro bn postApostB_stB0 =>
                   ex_intro
                     (fun an0 : nat =>
                      exists (a : ST) (an1 : nat) (stA : ST),
                        (a = x0 /\ an1 = 0 /\ stA = x0) /\
                        stA = a /\
                        an0 = length stA /\ stB = bare_list_insert x stA)
                     (an + bn)
                     (ex_intro
                        (fun a : ST =>
                         exists (an0 : nat) (stA : ST),
                           (a = x0 /\ an0 = 0 /\ stA = x0) /\
                           stA = a /\
                           an + bn = length stA /\
                           stB = bare_list_insert x stA) x0
                        (ex_intro
                           (fun an0 : nat =>
                            exists stA : ST,
                              (x0 = x0 /\ an0 = 0 /\ stA = x0) /\
                              stA = x0 /\
                              an + bn = length stA /\
                              stB = bare_list_insert x stA) an
                           (ex_intro
                              (fun stA : ST =>
                               (x0 = x0 /\ an = 0 /\ stA = x0) /\
                               stA = x0 /\
                               an + bn = length stA /\
                               stB = bare_list_insert x stA) x0
                              (conj postA_stA
                                 (postApostB_stB0 x0 an postA_stA)))))
               end
           end) y).
  
  destruct (insert_obligation_6 x x0
              match
                insert_obligation_1 x
                  (exist (fun _ : ST => True) x0 preA_st0)
              with
              | ex_intro x1 H0 =>
                  ex_intro
                    (fun st0 : ST =>
                     exists (an : nat) (stA : ST),
                       x0 = st0 /\ an = 0 /\ stA = st0) x0
                    (ex_intro
                       (fun an : nat =>
                        exists stA : ST, x0 = x0 /\ an = 0 /\ stA = x0) x1
                       (ex_intro
                          (fun stA : ST => x0 = x0 /\ x1 = 0 /\ stA = x0) x0
                          H0))
              end
              (exist (fun st : ST => st = x0) x0
                 match
                   insert_obligation_1 x
                     (exist (fun _ : ST => True) x0 preA_st0)
                 with
                 | ex_intro x1 H0 => postApreB x0 x1 x0 H0
                 end))
  as [preA_st1 postApreB0].
  simpl in *.
  
  clear y.

program_simpl.
  
  simpl in *.  
  remember (insert_obligation_7 x x0
             (ex_intro
                (fun st0 : ST =>
                 exists (an : nat) (stA : ST),
                   x0 = st0 /\ an = 0 /\ stA = st0) x0
                (ex_intro
                   (fun an : nat =>
                    exists stA : ST, x0 = x0 /\ an = 0 /\ stA = x0) x1
                   (ex_intro (fun stA : ST => x0 = x0 /\ x1 = 0 /\ stA = x0)
                      x0 a)))
             (exist (fun st : ST => st = x0) x0 (e x0 x1 x0 a))).
  simpl in *.
  
  
  eauto.
  
  exists (length postl).
  destruct (list_insert x postl (exist (fun _ : ST => True) postl I))
    as [[a st'] [an [EQa [EQan EQst']]]].
  
  eauto.
  split. auto.
  
  eauto.

End dumb_list.

Recursive Extraction insert.
