Require Import Program.

Definition CS_Pre (ST:Set) : Type
  := ST -> Prop.
Hint Unfold CS_Pre.

Definition CS_Post (ST:Set) (A:Set) : Type :=
  ST -> A -> nat -> ST -> Prop.
Hint Unfold CS_Post.

Definition
  CS (ST:Set) (pre : CS_Pre ST) (A : Set) (post : CS_Post ST A) : Set :=
  forall st : ST,
    pre st ->
    { (a, st') : A * ST |
      (* cs final *)
      exists an, post st a an st' }.
Hint Unfold CS.

Program Definition weaken (ST:Set)
  (pre : CS_Pre ST) (pre' : CS_Pre ST)
  (A:Set)  
  (post : CS_Post ST A) (post' : CS_Post ST A)
  (am:CS ST pre A post)
  (pre_stronger : (forall st, pre' st -> pre st))
  (post_weaker :
    (forall st a an st',
      post st a an st' ->
      post' st a an st')) :
  (CS ST pre' A post').
Proof.
  intros.
  intros st pre_st.
  edestruct (am st) as [[a st'] post_st'].
  auto.
  exists (a, st').
  destruct post_st' as [an post_st'].
  eauto.
Defined.

Definition top (ST:Set) : CS_Pre ST := fun st => True.
Hint Unfold top.

Program Definition ret (ST:Set) (A : Set) (post : CS_Post ST A) 
  : forall av,
    (forall st, post st av 0 st) ->
    CS ST (top ST) A (fun st ap an st' => st = st' /\ ap = av /\ post st ap an st').
Proof.
  intros ST A post av CPav0.
  unfold CS.
  intros st pre_st.
  exists (av, st).
  eauto.
Defined.
Hint Unfold ret.

Program Definition bind:
  forall (ST:Set) (A:Set)
    (preA : CS_Pre ST) (postA : CS_Post ST A) (am:(CS ST preA A postA))
    (B:Set) (preB : A -> nat -> CS_Pre ST) (postB : A -> CS_Post ST B)
    (bf:(forall (a : A) (postA_stA : (exists st an stA, postA st a an stA)),
      (CS
        ST
        (* bf pre *)
        (fun stA =>
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
    (fun st0 b cn stB =>
      exists a an stA bn,
        cn = an + bn /\
        postA st0 a an stA /\
        postB a stA b cn stB).
Proof.
  intros.
  intros st0 [preA_st0 postApreB].
  edestruct (am st0 preA_st0)
   as [[av stA] postA_stA].
  simpl in *.

  assert (exists st an stA, postA st av an stA) as epostA_stA.
  destruct postA_stA. eauto.

  edestruct
  (bf av epostA_stA stA)
  as [[bv stB] postApostB_stB].

  destruct postA_stA. eauto.

  clear epostA_stA.
  exists (bv, stB).
  destruct postA_stA as [an postA_stA].
  destruct postApostB_stB as [bn postB_stB].
  simpl in *.
  exists (an + bn). exists av.
  exists an. exists stA.
  exists bn. eauto.
Defined.
Hint Unfold bind.

Program Definition get (ST:Set):
  CS ST (top ST) ST (fun st0 st1 gn st2 => st0 = st1 /\ gn = 0 /\ st2 = st0).
Proof.
  intros ST.
  intros st0 pre_st0.
  exists (st0, st0). simpl.
  eauto.
Defined.
Hint Unfold get.

Program Definition put (ST:Set) (st2:ST) :
  CS ST (top ST) () (fun _ _ pn st2' => pn = 0 /\ st2 = st2').
Proof.
  intros ST st2 st0 pre_st0.
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
  intros st0 pre_st0. simpl.
  edestruct (am st0 pre_st0)
   as [[av stA] post_stA].
  simpl in *.
  exists (av, stA).
  destruct post_stA as [an post_stA].
  exists (an + k). eauto.
Defined.
Hint Unfold inc.
    
(* xxx example inline for testing *)

Require Import Omega.
  
Inductive SnocOf (x:nat) : (list nat) -> (list nat) -> Prop :=
| SO_nil :
  SnocOf x nil (cons x nil)
| SO_cons :
  forall y sl sl',
    SnocOf x sl sl' ->
    SnocOf x (cons y sl) (cons y sl').
Hint Constructors SnocOf.

Program Fixpoint snoc (ST:Set) x (l:list nat) :
  (CS ST (fun st => True) _
    (fun st r ln st' =>
      SnocOf x l r /\ ln = length l /\ st' = st))
  :=
  match l with
    | nil =>
      (@ret ST _
        (fun st r ln st' =>
          SnocOf x l r /\ ln = 0 /\ st' = st)
        (cons x nil) _)
    | cons y sl =>
      (@weaken _ _ _ _ _ _
        (@bind ST
          _ _ _ (snoc ST x sl)
          
          _
          (fun sl' sl'n st =>
            SnocOf x sl sl' /\ sl'n = length sl)
          (fun sl' st r bn st' =>
            SnocOf x l r /\ bn = length l /\ st' = st)
          (fun sl' psl' =>
            (@weaken _ _ _ _ _ _
              (@inc ST 1 (fun st => SnocOf x sl sl')
                _
                (fun st r bn st' =>
                  SnocOf x l r /\ bn = 1 /\ st' = st)
                (@weaken _ _ _ _ _ _
                  (@ret ST _
                    (fun st r bn st' =>
                      SnocOf x l r /\ bn = 0 /\ st' = st)
                    (cons y sl') _)
                  _ _))
              _ _)))
        _ _)
  end.

Next Obligation.
  eauto.
Defined.

Next Obligation.
  simpl. repeat split; auto.
  omega.
Defined.

Next Obligation.
  intuition.
Defined.

Definition ST := list nat.

Program Definition store_snoc (x:nat) :
  @CS ST
  (fun st => True)
  _
  (fun st _ n st' => n = length st /\ SnocOf x st st')
  :=
  (@weaken _ _ _ _ _ _
    (@bind ST

      _ _ _ (@get ST)

      _
      (fun av an st => an = 0 /\ st = av)
      (fun av st _ bn st' =>
        st = av /\ bn = length st /\ SnocOf x st st')
      (fun l pl =>
        (@weaken _ _ _ _ _ _
          (@bind ST

            _ 
            (fun st => st = l)
            (fun st l' l'n st' =>
              SnocOf x l l' /\ l'n = length l /\ st' = st)
            (@weaken _ _ _ _ _ _ (snoc ST x l) _ _)
            
            _
            (fun l' l'n st =>
              SnocOf x l l' /\ l'n = length l /\ st = l)
            (fun l' st _ bn st' =>
              bn = length l /\ st' = l')
            (fun l' pl' =>
              (@weaken _ _ _ _ _ _ (@put ST l') _ _)))
          _ _)))
    _ _).

Obligation Tactic := idtac.

Next Obligation.
  intros x l.
  intros [st [an [stA [EQl [EQan EQstA]]]]].
  subst l an stA.
  intros st0 _.
  intros an st'.
  intros [l [ln [stA [pn [EQan [[SO [EQln EQstA]] post]]]]]].
  subst an ln stA.
  destruct post as [EQ EQst'].
  subst l.
  replace pn with 0 in *. clear EQ.
  intros an [EQan EQst0].
  subst an st0.
  repeat split; auto.
  omega.
  omega.
Defined.

Next Obligation.
  intuition. subst. auto.
Defined.
  
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

Extraction Inline ret bind inc get put weaken.
Extraction Inline projT1 projT2.

Recursive Extraction store_snoc.
