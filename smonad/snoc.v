Require Import Omega.
Require Import Braun.smonad.smonad.
  
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
      (@weaken _ _ _ _ _ _
        (@ret ST _
          (fun st r ln st' =>
            SnocOf x l r /\ ln = 0 /\ st' = st)
          (cons x nil) _)
        _ _)
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

            _ _ _ (snoc ST x l)            
            
            _
            (fun l' l'n st =>
              SnocOf x l l' /\ l'n = length l /\ st = l)
            (fun l' st _ bn st' =>
              bn = length l /\ st' = l')
            (fun l' pl' =>
              (@weaken _ _ _ _ _ _ (@put ST l') _ _)))
          _ _)))
    _ _).

(* Coq's default tactic doesn't do the "occurs" check when rewriting *)
Obligation Tactic := idtac.

Next Obligation.
  intros x l.
  intros [st [an [stA [EQl [EQan EQstA]]]]].
  subst l an stA.
  intros st0 _.
  intros an st'.
  intros [PRE [l [ln [stA [pn [EQan [[SO [EQln EQstA]] post]]]]]]].
  destruct PRE as [st1 [an0 [[EQst1 [EQan0 EQst0]] [EQan0' EQst0']]]].
  destruct post as [EQ EQst'].
  subst an ln stA l.
  subst st1 an0 st0. clear EQan0' EQst0.
  replace pn with 0 in *. clear EQ.
  intros an [EQan EQst0].
  subst an. clear EQst0.
  repeat split; auto.
  omega.
  omega.
Defined.

Next Obligation.
  intuition. subst. auto.
Defined.
