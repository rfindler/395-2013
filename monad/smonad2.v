Require Import Program.

Definition CS_Pre (ST:Set) : Type
  := ST -> Prop.
Hint Unfold CS_Pre.

Definition CS_Post (ST:Set) (A:Set) : Type :=
  ST -> A -> nat -> ST -> Prop.
Hint Unfold CS_Post.

Definition CS_Arg (ST:Set) (pre : CS_Pre ST) := { st : ST | pre st }.
Hint Unfold CS_Arg.

Definition
  CS (ST:Set) (pre : CS_Pre ST) (A : Set) (post : CS_Post ST A) : Set :=
  forall st : (CS_Arg ST pre),
    { (a, st') : A * ST |
      (* cs final *)
      exists an, post (proj1_sig st) a an st' }.
Hint Unfold CS.

Definition top (ST:Set) : CS_Pre ST := fun st => True.
Hint Unfold top.

Program Definition ret (ST:Set) (A : Set) (post : CS_Post ST A) 
  : forall av,
    (forall st, post st av 0 st) ->
    CS ST (top ST) A (fun st ap an st' => st = st' /\ ap = av /\ post st ap an st').
Proof.
  intros ST A post av CPav0.
  unfold CS.
  intros [st pre_st].
  exists (av, st).
  eauto.
Defined.
Hint Unfold ret.

Program Definition bind:
  forall (ST:Set) (A:Set)
    (preA : CS_Pre ST) (postA : CS_Post ST A) (am:(CS ST preA A postA))
    (B:Set) (preB : A -> nat -> CS_Pre ST) (postB : A -> CS_Post ST B)
    (bf:(forall (a : A),
      (CS
        ST
        (* bf pre *)
        (fun stA =>
          (* forall an,
            (exists st, postA st a an stA) ->
            preB a an stA) *)
          exists st an,
            postA st a an stA /\
            preB a an stA)
        B
        (* bf post *)
        (fun stA bv bn stB =>
          forall an,
            preB a an stA ->
            postB a stA bv (an+bn) stB)))),
    CS ST
    (* bind pre *)
    (fun st0 =>
      preA st0 /\
      (forall a an stA,
        postA st0 a an stA ->
        preB a an stA))
    B
    (fun st0 b bn stB =>
      exists a an stA,
        postA st0 a an stA /\
        postB a stA b (an+bn) stB).
Proof.
  intros.
  intros [st0 [preA_st0 postApreB]].
  edestruct (am (exist preA st0 preA_st0))
   as [[av stA] postA_stA].
  simpl in *.

  assert ((fun stA : ST =>
    exists (st : ST) (an : nat), postA st av an stA /\ preB av an stA)
  stA) as preB_stA.
  destruct postA_stA as [an postA_stA]. eauto. 
  
  edestruct
  (bf av (exist (fun stA : ST =>
    exists (st : ST) (an : nat), postA st av an stA /\ preB av an stA) stA preB_stA))
  as [[bv stB] postApostB_stB].
  exists (bv, stB).
  destruct postA_stA as [an postA_stA].
  destruct postApostB_stB as [bn postB_stB].
  simpl in *.
  exists bn. exists av.
  exists an. exists stA.
  split. auto.
  eapply postB_stB.
  eauto.
Defined.
Hint Unfold bind.

Program Definition get (ST:Set):
  CS ST (top ST) ST (fun st0 st1 gn st2 => st0 = st1 /\ gn = 0 /\ st2 = st0).
Proof.
  intros ST.
  intros [st0 pre_st0].
  exists (st0, st0). simpl.
  eauto.
Defined.
Hint Unfold get.

Program Definition put (ST:Set) (st2:ST) :
  CS ST (top ST) () (fun _ _ pn st2' => pn = 0 /\ st2 = st2').
Proof.
  intros ST st2 [st0 pre_st0].
  exists ((), st2).
  eauto.
Defined.
Hint Unfold put.

Program Definition inc (ST:Set) (k:nat) :
  forall (pre : CS_Pre ST) (A:Set) (post : CS_Post ST A),
    CS ST pre A 
    (fun st a an st' =>
      forall am,
        an + k = am ->
        post st a am st') ->
    CS ST pre A post.
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
Hint Unfold inc.
    
(* xxx example inline for testing *)

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
  (CS ST (fun st => True) (list nat)
    (fun st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st))
  :=
  match l with
    | nil =>
      (@ret ST (list nat)
        (fun st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st)
        (cons x nil) _)
    | cons y sl =>
      (@bind ST
        (list nat)
        (fun st => True)
        (fun st r ln st' => r = bare_list_insert x sl /\ ln = length sl /\ st' = st)
        (list_insert x sl)
        
        (list nat)
        (fun sl' sl'n st => sl'n = length sl /\ sl' = bare_list_insert x sl)
        (fun sl' st r ln st' => r = bare_list_insert x l /\ ln = length l /\ st' = st)
        (fun sl' =>
          (@inc ST 1 (fun st => True) (list nat)
            (fun st r ln st' => r = (cons y sl') /\ ln = 1 /\ st' = st)
            (@ret ST (list nat)
              (fun st r ln st' => r = (cons y sl') /\ ln = 0 /\ st' = st)
              (cons y sl') _))))
  end.

Next Obligation. (* 1st return proof *)
  rename x0 into st.
  destruct st as [st Pre_st].
  simpl. eauto.
Defined.

Next Obligation. (* 2nd return proof *)
  simpl.
  rename x0 into st.
  destruct st as [st Pre_st].
  simpl.
  exists 0.
  intros am. simpl.
  intros EQ. subst am.
  auto.
Defined.

Next Obligation. (* bf post *)  
  rename x0 into st.
  exists 1. intros an [EQ1 EQ2]. subst an.
  simpl. subst sl'.
  repeat split; auto.
  omega.
Defined.

Next Obligation. (* bind pre *)
  intuition.
Defined.

Next Obligation. (* cs final *)
  exists (S (length sl)).
  auto.
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
  (fun av an st => an = 0 /\ st = av)
  (fun av st _ bn st' =>
    st = av /\ bn = length st /\ st' = bare_list_insert x st)
  (fun l =>
    (@bind ST

      ST 
      (fun st => st = l)
      (fun st l' l'n st' =>
        l' = bare_list_insert x st /\ l'n = length st /\ st' = st)
      (list_insert x l)
      
      ()
      (fun l' l'n st =>  l'n = length st /\ l' = bare_list_insert x st)
      (fun l' st _ bn st' =>
        l' = bare_list_insert x st /\ bn = length st /\ st' = l')
      (fun l' =>
        (@put ST l')))).

Next Obligation.
  rename x0 into st.
  destruct st as [st Pre_st].
  simpl. eauto.
Defined.

Next Obligation.
  rename x0 into st.
  destruct st as [st Pre_st].
  simpl.

  destruct (list_insert x l
          (exist (fun _ : ST => True) st
             (insert_obligation_2 x l
                (exist (fun st0 : ST => st0 = l) st Pre_st))))
    as [[a st'] [an [EQa [EQan EQst']]]].
  simpl in *.
  subst a an st' st.
  exists (length l).
  eauto.
Defined.

Next Obligation.
  rename x0 into st.
  destruct st as [st [st' [an [[EQl' [EQan EQst']] [EQan2 EQl'2]]]]].
  subst l' an st'.
  simpl.
  exists 0. intros an [EQan EQl].
  subst an. auto.
Defined.

Next Obligation.
  rename x0 into st.
  destruct st as [st [st' [an [[EQl [EQan stA]] [EQan2 EQstA]]]]].
  simpl. subst st' an st.
  split; auto. clear EQan2 stA.
  intros a an stA [EQa [EQan EQstA]].
  subst a an stA.
  auto.
Defined.

Next Obligation.
  rename x0 into st.
  destruct st as [st Pre_st].
  simpl.
  destruct Pre_st as [st' [an [[EQl [EQan EQst]] [EQan2 EQst2]]]].
  subst st' an st. simpl.
  clear EQan2.
  destruct (list_insert x l
                (exist (fun _ : ST => True) l
                   (insert_obligation_2 x l
                     (exist (fun st : ST => st = l) l EQst))))
  as [[l' st'] [an [EQl' [EQan EQst']]]].
  simpl in *.
  subst l' an st'. clear EQst.
  exists (length l).
  intros an [EQan EQl].
  subst an. simpl. auto.
Defined.

Next Obligation.
  rename x0 into st.
  destruct st as [st Pre_st].
  split; auto.
  intros a an stA. simpl.
  intros [EQa [EQan EQstA]].
  subst. auto.
Defined.

Next Obligation.
  rename x0 into st.
  destruct st as [st Pre_st].
  simpl in *.

  (* 1277 lines! *)
Admitted.

Extract Inductive unit => "unit" [ "tt" ].
Extract Inductive bool => "bool" [ "false" "true" ].
Extract Inductive sumbool => "bool" [ "false" "true" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => 
"int" [ "0" "succ" ]
      "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "fun x y -> x + y".
Extract Constant mult => "fun x y -> x * y".
Extract Constant minus => "fun x y -> x - y".

Extraction Inline ret bind inc get put.
Extraction Inline projT1 projT2.

Recursive Extraction insert.
