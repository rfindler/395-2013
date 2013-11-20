(* Copyright (c) 2011-2012, Adam Chlipala
 * 
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(* begin hide *)

Require Import List.

Require Import CpdtTactics.

Set Implicit Arguments.

(* end hide *)

(** %\part{Proof Engineering}

   \chapter{Proof Search by Logic Programming}% *)

(** The Curry-Howard correspondence tells us that proving is "just" programming, but the pragmatics of the two activities are very different.  Generally we care about properties of a program besides its type, but the same is not true about proofs.  Any proof of a theorem will do just as well.  As a result, automated proof search is conceptually simpler than automated programming.

   The paradigm of %\index{logic programming}%logic programming%~\cite{LogicProgramming}%, as embodied in languages like %\index{Prolog}%Prolog%~\cite{Prolog}%, is a good match for proof search in higher-order logic.  This chapter introduces the details, attempting to avoid any dependence on past logic programming experience. *)


(** * Introducing Logic Programming *)

(** Recall the definition of addition from the standard library. *)

Print plus.
(** %\vspace{-.15in}%[[
plus = 
fix plus (n m : nat) : nat := match n with
                              | 0 => m
                              | S p => S (plus p m)
                              end

]]

This is a recursive definition, in the style of functional programming.  We might also follow the style of logic programming, which corresponds to the inductive relations we have defined in previous chapters. *)

Inductive plusR : nat -> nat -> nat -> Prop :=
| PlusO : forall m, plusR O m m
| PlusS : forall n m r, plusR n m r
  -> plusR (S n) m (S r).

(** Intuitively, a fact [plusR n m r] only holds when [plus n m = r].  It is not hard to prove this correspondence formally. *)

(* begin thide *)
Hint Constructors plusR.
(* end thide *)

Theorem plus_plusR : forall n m,
  plusR n m (n + m).
(* begin thide *)
  induction n; crush.
Qed.
(* end thide *)

Theorem plusR_plus : forall n m r,
  plusR n m r
  -> r = n + m.
(* begin thide *)
  induction 1; crush.
Qed.
(* end thide *)

(** With the functional definition of [plus], simple equalities about arithmetic follow by computation. *)

Example four_plus_three : 4 + 3 = 7.
(* begin thide *)
  reflexivity.
Qed.
(* end thide *)

(* begin hide *)
(* begin thide *)
Definition er := @eq_refl.
(* end thide *)
(* end hide *)

Print four_plus_three.
(** %\vspace{-.15in}%[[
four_plus_three = eq_refl
]]

With the relational definition, the same equalities take more steps to prove, but the process is completely mechanical.  For example, consider this simple-minded manual proof search strategy.  The steps with error messages shown afterward will be omitted from the final script.
*)

Example four_plus_three' : plusR 4 3 7.
(* begin thide *)
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?24 ?24" with "plusR 4 3 7".
>> *)
  apply PlusS.
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?25 ?25" with "plusR 3 3 6".
>> *)
  apply PlusS.
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?26 ?26" with "plusR 2 3 5".
>> *)
  apply PlusS.
(** %\vspace{-.2in}%[[
  apply PlusO.
]]
%\vspace{-.2in}%
<<
Error: Impossible to unify "plusR 0 ?27 ?27" with "plusR 1 3 4".
>> *)
  apply PlusS.
  apply PlusO.

(** At this point the proof is completed.  It is no doubt clear that a simple procedure could find all proofs of this kind for us.  We are just exploring all possible proof trees, built from the two candidate steps [apply PlusO] and [apply PlusS].  The built-in tactic %\index{tactics!auto}%[auto] follows exactly this strategy, since above we used %\index{Vernacular commands!Hint Constructors}%[Hint Constructors] to register the two candidate proof steps as hints. *)

Restart.
  auto.
Qed.
(* end thide *)

Print four_plus_three'.
(** %\vspace{-.15in}%[[
four_plus_three' = PlusS (PlusS (PlusS (PlusS (PlusO 3))))
]]
*)

(** Let us try the same approach on a slightly more complex goal. *)

Example five_plus_three : plusR 5 3 8.
(* begin thide *)
  auto.

(** This time, [auto] is not enough to make any progress.  Since even a single candidate step may lead to an infinite space of possible proof trees, [auto] is parameterized on the maximum depth of trees to consider.  The default depth is 5, and it turns out that we need depth 6 to prove the goal. *)

  auto 6.

(** Sometimes it is useful to see a description of the proof tree that [auto] finds, with the %\index{tactics!info}%[info] tactical.  (This tactical is not available in Coq 8.4 as of this writing, but I hope it reappears soon.  The special case %\index{tactics!info\_auto}%[info_auto] tactic is provided as a chatty replacement for [auto].) *)

Restart.
  info auto 6.
(** %\vspace{-.15in}%[[
 == apply PlusS; apply PlusS; apply PlusS; apply PlusS; 
    apply PlusS; apply PlusO.
]]
*)
Qed.
(* end thide *)

(** The two key components of logic programming are%\index{backtracking}% _backtracking_ and%\index{unification}% _unification_.  To see these techniques in action, consider this further silly example.  Here our candidate proof steps will be reflexivity and quantifier instantiation. *)

Example seven_minus_three : exists x, x + 3 = 7.
(* begin thide *)
(** For explanatory purposes, let us simulate a user with minimal understanding of arithmetic.  We start by choosing an instantiation for the quantifier.  Recall that [ex_intro] is the constructor for existentially quantified formulas. *)

  apply ex_intro with 0.
(** %\vspace{-.2in}%[[
  reflexivity.
]]
%\vspace{-.2in}%
<<
  Error: Impossible to unify "7" with "0 + 3".
>>

This seems to be a dead end.  Let us _backtrack_ to the point where we ran [apply] and make a better alternate choice.
*)

Restart.
  apply ex_intro with 4.
  reflexivity.
Qed.
(* end thide *)

(** The above was a fairly tame example of backtracking.  In general, any node in an under-construction proof tree may be the destination of backtracking an arbitrarily large number of times, as different candidate proof steps are found not to lead to full proof trees, within the depth bound passed to [auto].

   Next we demonstrate unification, which will be easier when we switch to the relational formulation of addition. *)

Example seven_minus_three' : exists x, plusR x 3 7.
(* begin thide *)
(** We could attempt to guess the quantifier instantiation manually as before, but here there is no need.  Instead of [apply], we use %\index{tactics!eapply}%[eapply], which proceeds with placeholder%\index{unification variable}% _unification variables_ standing in for those parameters we wish to postpone guessing. *)

  eapply ex_intro.
(** [[
1 subgoal
  
  ============================
   plusR ?70 3 7
]]

Now we can finish the proof with the right applications of [plusR]'s constructors.  Note that new unification variables are being generated to stand for new unknowns. *)

  apply PlusS.
(** [[
  ============================
   plusR ?71 3 6
]]
*)
  apply PlusS. apply PlusS. apply PlusS.
(** [[
  ============================
   plusR ?74 3 3
]]
*)
  apply PlusO.

(** The [auto] tactic will not perform these sorts of steps that introduce unification variables, but the %\index{tactics!eauto}%[eauto] tactic will.  It is helpful to work with two separate tactics, because proof search in the [eauto] style can uncover many more potential proof trees and hence take much longer to run. *)

Restart.
  info eauto 6.
(** %\vspace{-.15in}%[[
 == eapply ex_intro; apply PlusS; apply PlusS; 
    apply PlusS; apply PlusS; apply PlusO.
]]
*)
Qed.
(* end thide *)

(** This proof gives us our first example where logic programming simplifies proof search compared to functional programming.  In general, functional programs are only meant to be run in a single direction; a function has disjoint sets of inputs and outputs.  In the last example, we effectively ran a logic program backwards, deducing an input that gives rise to a certain output.  The same works for deducing an unknown value of the other input. *)

Example seven_minus_four' : exists x, plusR 4 x 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

(** By proving the right auxiliary facts, we can reason about specific functional programs in the same way as we did above for a logic program.  Let us prove that the constructors of [plusR] have natural interpretations as lemmas about [plus].  We can find the first such lemma already proved in the standard library, using the %\index{Vernacular commands!SearchRewrite}%[SearchRewrite] command to find a library function proving an equality whose lefthand or righthand side matches a pattern with wildcards. *)

(* begin thide *)
SearchRewrite (O + _).
(** %\vspace{-.15in}%[[
plus_O_n: forall n : nat, 0 + n = n
]]

The command %\index{Vernacular commands!Hint Immediate}%[Hint Immediate] asks [auto] and [eauto] to consider this lemma as a candidate step for any leaf of a proof tree. *)

Hint Immediate plus_O_n.

(** The counterpart to [PlusS] we will prove ourselves. *)

Lemma plusS : forall n m r,
  n + m = r
  -> S n + m = S r.
  crush.
Qed.

(** The command %\index{Vernacular commands!Hint Resolve}%[Hint Resolve] adds a new candidate proof step, to be attempted at any level of a proof tree, not just at leaves. *)

Hint Resolve plusS.
(* end thide *)

(** Now that we have registered the proper hints, we can replicate our previous examples with the normal, functional addition [plus]. *)

Example seven_minus_three'' : exists x, x + 3 = 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

Example seven_minus_four : exists x, 4 + x = 7.
(* begin thide *)
  eauto 6.
Qed.
(* end thide *)

(** This new hint database is far from a complete decision procedure, as we see in a further example that [eauto] does not finish. *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
(* begin thide *)
  eauto 6.
Abort.
(* end thide *)

(** A further lemma will be helpful. *)

(* begin thide *)
Lemma plusO : forall n m,
  n = m
  -> n + 0 = m.
  crush.
Qed.

Hint Resolve plusO.
(* end thide *)

(** Note that, if we consider the inputs to [plus] as the inputs of a corresponding logic program, the new rule [plusO] introduces an ambiguity.  For instance, a sum [0 + 0] would match both of [plus_O_n] and [plusO], depending on which operand we focus on.  This ambiguity may increase the number of potential search trees, slowing proof search, but semantically it presents no problems, and in fact it leads to an automated proof of the present example. *)

Example seven_minus_four_zero : exists x, 4 + x + 0 = 7.
(* begin thide *)
  eauto 7.
Qed.
(* end thide *)

(** Just how much damage can be done by adding hints that grow the space of possible proof trees?  A classic gotcha comes from unrestricted use of transitivity, as embodied in this library theorem about equality: *)

Check eq_trans.
(** %\vspace{-.15in}%[[
eq_trans
     : forall (A : Type) (x y z : A), x = y -> y = z -> x = z
]]
*)

(** Hints are scoped over sections, so let us enter a section to contain the effects of an unfortunate hint choice. *)

Section slow.
  Hint Resolve eq_trans.

  (** The following fact is false, but that does not stop [eauto] from taking a very long time to search for proofs of it.  We use the handy %\index{Vernacular commands!Time}%[Time] command to measure how long a proof step takes to run.  None of the following steps make any progress. *)

  Example zero_minus_one : exists x, 1 + x = 0.
    Time eauto 1.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.u,0.s)
>>
*)

    Time eauto 2.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.u,0.s)
>>
*)

    Time eauto 3.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.008u,0.s)
>>
*)

    Time eauto 4.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.068005u,0.004s)
>>
*)

    Time eauto 5.
(** %\vspace{-.15in}%
<<
Finished transaction in 2. secs (1.92012u,0.044003s)
>>
*)

(** We see worrying exponential growth in running time, and the %\index{tactics!debug}%[debug] tactical helps us see where [eauto] is wasting its time, outputting a trace of every proof step that is attempted.  The rule [eq_trans] applies at every node of a proof tree, and [eauto] tries all such positions. *)

(* begin hide *)
(* begin thide *)
Definition syms := (eq_sym, plus_n_O, eq_add_S, f_equal2).
(* end thide *)
(* end hide *)

    debug eauto 3.
(** [[
1 depth=3 
1.1 depth=2 eapply ex_intro
1.1.1 depth=1 apply plusO
1.1.1.1 depth=0 eapply eq_trans
1.1.2 depth=1 eapply eq_trans
1.1.2.1 depth=1 apply plus_n_O
1.1.2.1.1 depth=0 apply plusO
1.1.2.1.2 depth=0 eapply eq_trans
1.1.2.2 depth=1 apply @eq_refl
1.1.2.2.1 depth=0 apply plusO
1.1.2.2.2 depth=0 eapply eq_trans
1.1.2.3 depth=1 apply eq_add_S ; trivial
1.1.2.3.1 depth=0 apply plusO
1.1.2.3.2 depth=0 eapply eq_trans
1.1.2.4 depth=1 apply eq_sym ; trivial
1.1.2.4.1 depth=0 eapply eq_trans
1.1.2.5 depth=0 apply plusO
1.1.2.6 depth=0 apply plusS
1.1.2.7 depth=0 apply f_equal (A:=nat)
1.1.2.8 depth=0 apply f_equal2 (A1:=nat) (A2:=nat)
1.1.2.9 depth=0 eapply eq_trans
]]
*)
  Abort.
End slow.

(** Sometimes, though, transitivity is just what is needed to get a proof to go through automatically with [eauto].  For those cases, we can use named%\index{hint databases}% _hint databases_ to segregate hints into different groups that may be called on as needed.  Here we put [eq_trans] into the database [slow]. *)

(* begin thide *)
Hint Resolve eq_trans : slow.
(* end thide *)

Example three_minus_four_zero : exists x, 1 + x = 0.
(* begin thide *)
  Time eauto.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.004u,0.s)
>>

This [eauto] fails to prove the goal, but at least it takes substantially less than the 2 seconds required above! *)

Abort.
(* end thide *)

(** One simple example from before runs in the same amount of time, avoiding pollution by transitivity. *)

Example seven_minus_three_again : exists x, x + 3 = 7.
(* begin thide *)
  Time eauto 6.
(** %\vspace{-.15in}%
<<
Finished transaction in 0. secs (0.004001u,0.s)
>>
%\vspace{-.2in}% *)

Qed.
(* end thide *)

(** When we _do_ need transitivity, we ask for it explicitly. *)

Example needs_trans : forall x y, 1 + x = y
  -> y = 2
  -> exists z, z + x = 3.
(* begin thide *)
  info eauto with slow.
(** %\vspace{-.2in}%[[
 == intro x; intro y; intro H; intro H0; simple eapply ex_intro; 
    apply plusS; simple eapply eq_trans.
    exact H.
    
    exact H0.
]]
*)
Qed.
(* end thide *)

(** The [info] trace shows that [eq_trans] was used in just the position where it is needed to complete the proof.  We also see that [auto] and [eauto] always perform [intro] steps without counting them toward the bound on proof tree depth. *)


(** * Searching for Underconstrained Values *)

(** Recall the definition of the list length function. *)

Print length.
(** %\vspace{-.15in}%[[
length = 
fun A : Type =>
fix length (l : list A) : nat :=
  match l with
  | nil => 0
  | _ :: l' => S (length l')
  end
]]

This function is easy to reason about in the forward direction, computing output from input. *)

Example length_1_2 : length (1 :: 2 :: nil) = 2.
  auto.
Qed.

Print length_1_2.
(** %\vspace{-.15in}%[[
length_1_2 = eq_refl
]]

As in the last section, we will prove some lemmas to recast [length] in logic programming style, to help us compute inputs from outputs. *)

(* begin thide *)
Theorem length_O : forall A, length (nil (A := A)) = O.
  crush.
Qed.

Theorem length_S : forall A (h : A) t n,
  length t = n
  -> length (h :: t) = S n.
  crush.
Qed.

Hint Resolve length_O length_S.
(* end thide *)

(** Let us apply these hints to prove that a [list nat] of length 2 exists.  (Here we register [length_O] with [Hint Resolve] instead of [Hint Immediate] merely as a convenience to use the same command as for [length_S]; [Resolve] and [Immediate] have the same meaning for a premise-free hint.) *)

Example length_is_2 : exists ls : list nat, length ls = 2.
(* begin thide *)
  eauto.
(** <<
No more subgoals but non-instantiated existential variables:
Existential 1 = ?20249 : [ |- nat]
Existential 2 = ?20252 : [ |- nat]
>>

Coq complains that we finished the proof without determining the values of some unification variables created during proof search.  The error message may seem a bit silly, since _any_ value of type [nat] (for instance, 0) can be plugged in for either variable!  However, for more complex types, finding their inhabitants may be as complex as theorem-proving in general.

The %\index{Vernacular commands!Show Proof}%[Show Proof] command shows exactly which proof term [eauto] has found, with the undetermined unification variables appearing explicitly where they are used. *)

  Show Proof.
(** <<
Proof: ex_intro (fun ls : list nat => length ls = 2)
         (?20249 :: ?20252 :: nil)
         (length_S ?20249 (?20252 :: nil)
            (length_S ?20252 nil (length_O nat)))
>>
%\vspace{-.2in}% *)

Abort.
(* end thide *)

(** We see that the two unification variables stand for the two elements of the list.  Indeed, list length is independent of data values.  Paradoxically, we can make the proof search process easier by constraining the list further, so that proof search naturally locates appropriate data elements by unification.  The library predicate [Forall] will be helpful. *)

(* begin hide *)
(* begin thide *)
Definition Forall_c := (@Forall_nil, @Forall_cons).
(* end thide *)
(* end hide *)

Print Forall.
(** %\vspace{-.15in}%[[
Inductive Forall (A : Type) (P : A -> Prop) : list A -> Prop :=
    Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (l : list A),
                  P x -> Forall P l -> Forall P (x :: l)
]]
*)

Example length_is_2 : exists ls : list nat, length ls = 2
  /\ Forall (fun n => n >= 1) ls.
(* begin thide *)
  eauto 9.
Qed.
(* end thide *)

(** We can see which list [eauto] found by printing the proof term. *)

(* begin hide *)
(* begin thide *)
Definition conj' := (conj, le_n).
(* end thide *)
(* end hide *)

Print length_is_2.
(** %\vspace{-.15in}%[[
length_is_2 = 
ex_intro
  (fun ls : list nat => length ls = 2 /\ Forall (fun n : nat => n >= 1) ls)
  (1 :: 1 :: nil)
  (conj (length_S 1 (1 :: nil) (length_S 1 nil (length_O nat)))
     (Forall_cons 1 (le_n 1)
        (Forall_cons 1 (le_n 1) (Forall_nil (fun n : nat => n >= 1)))))
]]
*)

(** Let us try one more, fancier example.  First, we use a standard higher-order function to define a function for summing all data elements of a list. *)

Definition sum := fold_right plus O.

(** Another basic lemma will be helpful to guide proof search. *)

(* begin thide *)
Lemma plusO' : forall n m,
  n = m
  -> 0 + n = m.
  crush.
Qed.

Hint Resolve plusO'.

(** Finally, we meet %\index{Vernacular commands!Hint Extern}%[Hint Extern], the command to register a custom hint.  That is, we provide a pattern to match against goals during proof search.  Whenever the pattern matches, a tactic (given to the right of an arrow [=>]) is attempted.  Below, the number [1] gives a priority for this step.  Lower priorities are tried before higher priorities, which can have a significant effect on proof search time. *)

Hint Extern 1 (sum _ = _) => simpl.
(* end thide *)

(** Now we can find a length-2 list whose sum is 0. *)

Example length_and_sum : exists ls : list nat, length ls = 2
  /\ sum ls = O.
(* begin thide *)
  eauto 7.
Qed.
(* end thide *)

(* begin hide *)
Print length_and_sum.
(* end hide *)

(** Printing the proof term shows the unsurprising list that is found.  Here is an example where it is less obvious which list will be used.  Can you guess which list [eauto] will choose? *)

Example length_and_sum' : exists ls : list nat, length ls = 5
  /\ sum ls = 42.
(* begin thide *)
  eauto 15.
Qed.
(* end thide *)

(* begin hide *)
Print length_and_sum'.
(* end hide *)

(** We will give away part of the answer and say that the above list is less interesting than we would like, because it contains too many zeroes.  A further constraint forces a different solution for a smaller instance of the problem. *)

Example length_and_sum'' : exists ls : list nat, length ls = 2
  /\ sum ls = 3
  /\ Forall (fun n => n <> 0) ls.
(* begin thide *)
  eauto 11.
Qed.
(* end thide *)

(* begin hide *)
Print length_and_sum''.
(* end hide *)

(** We could continue through exercises of this kind, but even more interesting than finding lists automatically is finding _programs_ automatically. *)


(** * Synthesizing Programs *)

(** Here is a simple syntax type for arithmetic expressions, similar to those we have used several times before in the book.  In this case, we allow expressions to mention exactly one distinguished variable. *)

Inductive exp : Set :=
| Const : nat -> exp
| Var : exp
| Plus : exp -> exp -> exp.

(** An inductive relation specifies the semantics of an expression, relating a variable value and an expression to the expression value. *)

Inductive eval (var : nat) : exp -> nat -> Prop :=
| EvalConst : forall n, eval var (Const n) n
| EvalVar : eval var Var var
| EvalPlus : forall e1 e2 n1 n2, eval var e1 n1
  -> eval var e2 n2
  -> eval var (Plus e1 e2) (n1 + n2).

(* begin thide *)
Hint Constructors eval.
(* end thide *)

(** We can use [auto] to execute the semantics for specific expressions. *)

Example eval1 : forall var, eval var (Plus Var (Plus (Const 8) Var)) (var + (8 + var)).
(* begin thide *)
  auto.
Qed.
(* end thide *)

(** Unfortunately, just the constructors of [eval] are not enough to prove theorems like the following, which depends on an arithmetic identity. *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
(* begin thide *)
  eauto.
Abort.
(* end thide *)

(** To help prove [eval1'], we prove an alternate version of [EvalPlus] that inserts an extra equality premise.  This sort of staging is helpful to get around limitations of [eauto]'s unification: [EvalPlus] as a direct hint will only match goals whose results are already expressed as additions, rather than as constants.  With the alternate version below, to prove the first two premises, [eauto] is given free reign in deciding the values of [n1] and [n2], while the third premise can then be proved by [reflexivity], no matter how each of its sides is decomposed as a tree of additions. *)

(* begin thide *)
Theorem EvalPlus' : forall var e1 e2 n1 n2 n, eval var e1 n1
  -> eval var e2 n2
  -> n1 + n2 = n
  -> eval var (Plus e1 e2) n.
  crush.
Qed.

Hint Resolve EvalPlus'.

(** Further, we instruct [eauto] to apply %\index{tactics!omega}%[omega], a standard tactic that provides a complete decision procedure for quantifier-free linear arithmetic.  Via [Hint Extern], we ask for use of [omega] on any equality goal.  The [abstract] tactical generates a new lemma for every such successful proof, so that, in the final proof term, the lemma may be referenced in place of dropping in the full proof of the arithmetic equality. *)

Hint Extern 1 (_ = _) => abstract omega.
(* end thide *)

(** Now we can return to [eval1'] and prove it automatically. *)

Example eval1' : forall var, eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

(* begin hide *)
(* begin thide *)
Definition e1s := eval1'_subproof.
(* end thide *)
(* end hide *)

Print eval1'.
(** %\vspace{-.15in}%[[
eval1' = 
fun var : nat =>
EvalPlus' (EvalVar var) (EvalPlus (EvalConst var 8) (EvalVar var))
  (eval1'_subproof var)
     : forall var : nat,
       eval var (Plus Var (Plus (Const 8) Var)) (2 * var + 8)
]]
*)

(** The lemma [eval1'_subproof] was generated by [abstract omega].

   Now we are ready to take advantage of logic programming's flexibility by searching for a program (arithmetic expression) that always evaluates to a particular symbolic value. *)

Example synthesize1 : exists e, forall var, eval var e (var + 7).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

Print synthesize1.
(** %\vspace{-.15in}%[[
synthesize1 = 
ex_intro (fun e : exp => forall var : nat, eval var e (var + 7))
  (Plus Var (Const 7))
  (fun var : nat => EvalPlus (EvalVar var) (EvalConst var 7))
]]
*)

(** Here are two more examples showing off our program synthesis abilities. *)

Example synthesize2 : exists e, forall var, eval var e (2 * var + 8).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

(* begin hide *)
Print synthesize2.
(* end hide *)

Example synthesize3 : exists e, forall var, eval var e (3 * var + 42).
(* begin thide *)
  eauto.
Qed.
(* end thide *)

(* begin hide *)
Print synthesize3.
(* end hide *)

(** These examples show linear expressions over the variable [var].  Any such expression is equivalent to [k * var + n] for some [k] and [n].  It is probably not so surprising that we can prove that any expression's semantics is equivalent to some such linear expression, but it is tedious to prove such a fact manually.  To finish this section, we will use [eauto] to complete the proof, finding [k] and [n] values automatically.

   We prove a series of lemmas and add them as hints.  We have alternate [eval] constructor lemmas and some facts about arithmetic. *)

(* begin thide *)
Theorem EvalConst' : forall var n m, n = m
  -> eval var (Const n) m.
  crush.
Qed.

Hint Resolve EvalConst'.

Theorem zero_times : forall n m r,
  r = m
  -> r = 0 * n + m.
  crush.
Qed.

Hint Resolve zero_times.

Theorem EvalVar' : forall var n,
  var = n
  -> eval var Var n.
  crush.
Qed.

Hint Resolve EvalVar'.

Theorem plus_0 : forall n r,
  r = n
  -> r = n + 0.
  crush.
Qed.

Theorem times_1 : forall n, n = 1 * n.
  crush.
Qed.

Hint Resolve plus_0 times_1.

(** We finish with one more arithmetic lemma that is particularly specialized to this theorem.  This fact happens to follow by the axioms of the _ring_ algebraic structure, so, since the naturals form a ring, we can use the built-in tactic %\index{tactics!ring}%[ring]. *)

Require Import Arith Ring.

Theorem combine : forall x k1 k2 n1 n2,
  (k1 * x + n1) + (k2 * x + n2) = (k1 + k2) * x + (n1 + n2).
  intros; ring.
Qed.

Hint Resolve combine.

(** Our choice of hints is cheating, to an extent, by telegraphing the procedure for choosing values of [k] and [n].  Nonetheless, with these lemmas in place, we achieve an automated proof without explicitly orchestrating the lemmas' composition. *)

Theorem linear : forall e, exists k, exists n,
  forall var, eval var e (k * var + n).
  induction e; crush; eauto.
Qed.

(* begin hide *)
Print linear.
(* end hide *)
(* end thide *)

(** By printing the proof term, it is possible to see the procedure that is used to choose the constants for each input term. *)


(** * More on [auto] Hints *)

(** Let us stop at this point and take stock of the possibilities for [auto] and [eauto] hints.  Hints are contained within _hint databases_, which we have seen extended in many examples so far.  When no hint database is specified, a default database is used.  Hints in the default database are always used by [auto] or [eauto].  The chance to extend hint databases imperatively is important, because, in Ltac programming, we cannot create "global variables" whose values can be extended seamlessly by different modules in different source files.  We have seen the advantages of hints so far, where [crush] can be defined once and for all, while still automatically applying the hints we add throughout developments.  In fact, [crush] is defined in terms of [auto], which explains how we achieve this extensibility.  Other user-defined tactics can take similar advantage of [auto] and [eauto].

The basic hints for [auto] and [eauto] are: %\index{Vernacular commands!Hint Immediate}%[Hint Immediate lemma], asking to try solving a goal immediately by applying a lemma and discharging any hypotheses with a single proof step each; %\index{Vernacular commands!Hint Resolve}%[Resolve lemma], which does the same but may add new premises that are themselves to be subjects of nested proof search; %\index{Vernacular commands!Hint Constructors}%[Constructors type], which acts like [Resolve] applied to every constructor of an inductive type; and %\index{Vernacular commands!Hint Unfold}%[Unfold ident], which tries unfolding [ident] when it appears at the head of a proof goal.  Each of these [Hint] commands may be used with a suffix, as in [Hint Resolve lemma : my_db], to add the hint only to the specified database, so that it would only be used by, for instance, [auto with my_db].  An additional argument to [auto] specifies the maximum depth of proof trees to search in depth-first order, as in [auto 8] or [auto 8 with my_db].  The default depth is 5.

All of these [Hint] commands can be expressed with a more primitive hint kind, [Extern].  A few more examples of [Hint Extern] should illustrate more of the possibilities. *)

Theorem bool_neq : true <> false.
(* begin thide *)
  auto.

  (** A call to [crush] would have discharged this goal, but the default hint database for [auto] contains no hint that applies. *)

Abort.

(* begin hide *)
(* begin thide *)
Definition boool := bool.
(* end thide *)
(* end hide *)

(** It is hard to come up with a [bool]-specific hint that is not just a restatement of the theorem we mean to prove.  Luckily, a simpler form suffices, by appealing to the built-in tactic %\index{tactics!congruence}%[congruence], a complete procedure for the theory of equality, uninterpreted functions, and datatype constructors. *)

Hint Extern 1 (_ <> _) => congruence.

Theorem bool_neq : true <> false.
  auto.
Qed.
(* end thide *)

(** A [Hint Extern] may be implemented with the full Ltac language.  This example shows a case where a hint uses a [match]. *)

Section forall_and.
  Variable A : Set.
  Variables P Q : A -> Prop.

  Hypothesis both : forall x, P x /\ Q x.

  Theorem forall_and : forall z, P z.
(* begin thide *)
    crush.

    (** The [crush] invocation makes no progress beyond what [intros] would have accomplished.  An [auto] invocation will not apply the hypothesis [both] to prove the goal, because the conclusion of [both] does not unify with the conclusion of the goal.  However, we can teach [auto] to handle this kind of goal. *)

    Hint Extern 1 (P ?X) =>
      match goal with
        | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
      end.

    auto.
  Qed.
(* end thide *)

  (** We see that an [Extern] pattern may bind unification variables that we use in the associated tactic.  The function [proj1] is from the standard library, for extracting a proof of [U] from a proof of [U /\ V]. *)

End forall_and.

(* begin hide *)
(* begin thide *)
Definition noot := (not, @eq).
(* end thide *)
(* end hide *)

(** After our success on this example, we might get more ambitious and seek to generalize the hint to all possible predicates [P].
   [[
Hint Extern 1 (?P ?X) =>
  match goal with
    | [ H : forall x, P x /\ _ |- _ ] => apply (proj1 (H X))
  end.
]]
<<
User error: Bound head variable
>>

   Coq's [auto] hint databases work as tables mapping%\index{head symbol}% _head symbols_ to lists of tactics to try.  Because of this, the constant head of an [Extern] pattern must be determinable statically.  In our first [Extern] hint, the head symbol was [not], since [x <> y] desugars to [not (eq x y)]; and, in the second example, the head symbol was [P].

   Fortunately, a more basic form of [Hint Extern] also applies.  We may simply leave out the pattern to the left of the [=>], incorporating the corresponding logic into the Ltac script. *)

Hint Extern 1 =>
  match goal with
    | [ H : forall x, ?P x /\ _ |- ?P ?X ] => apply (proj1 (H X))
  end.

(** Be forewarned that a [Hint Extern] of this kind will be applied at _every_ node of a proof tree, so an expensive Ltac script may slow proof search significantly. *)


(** * Rewrite Hints *)

(** Another dimension of extensibility with hints is rewriting with quantified equalities.  We have used the associated command %\index{Vernacular commands!Hint Rewrite}%[Hint Rewrite] in many examples so far.  The [crush] tactic uses these hints by calling the built-in tactic %\index{tactics!autorewrite}%[autorewrite].  Our rewrite hints have taken the form [Hint Rewrite lemma], which by default adds them to the default hint database [core]; but alternate hint databases may also be specified just as with, e.g., [Hint Resolve].

   The next example shows a direct use of [autorewrite].  Note that, while [Hint Rewrite] uses a default database, [autorewrite] requires that a database be named. *)

Section autorewrite.
  Variable A : Set.
  Variable f : A -> A.

  Hypothesis f_f : forall x, f (f x) = f x.

  Hint Rewrite f_f.

  Lemma f_f_f : forall x, f (f (f x)) = f x.
    intros; autorewrite with core; reflexivity.
  Qed.

  (** There are a few ways in which [autorewrite] can lead to trouble when insufficient care is taken in choosing hints.  First, the set of hints may define a nonterminating rewrite system, in which case invocations to [autorewrite] may not terminate.  Second, we may add hints that "lead [autorewrite] down the wrong path."  For instance: *)

  Section garden_path.
    Variable g : A -> A.
    Hypothesis f_g : forall x, f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with core.
      (** [[
============================
 g (g (g x)) = g x
          ]]
          *)

    Abort.

    (** Our new hint was used to rewrite the goal into a form where the old hint could no longer be applied.  This "non-monotonicity" of rewrite hints contrasts with the situation for [auto], where new hints may slow down proof search but can never "break" old proofs.  The key difference is that [auto] either solves a goal or makes no changes to it, while [autorewrite] may change goals without solving them.  The situation for [eauto] is slightly more complicated, as changes to hint databases may change the proof found for a particular goal, and that proof may influence the settings of unification variables that appear elsewhere in the proof state. *)

  Reset garden_path.

  (** The [autorewrite] tactic also works with quantified equalities that include additional premises, but we must be careful to avoid similar incorrect rewritings. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
    Hint Rewrite f_g.

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
      intros; autorewrite with core.
      (** [[
  ============================
   g (g (g x)) = g x

subgoal 2 is:
 P x
subgoal 3 is:
 P (f x)
subgoal 4 is:
 P (f x)
          ]]
          *)

    Abort.

    (** The inappropriate rule fired the same three times as before, even though we know we will not be able to prove the premises. *)

  Reset garden_path.

  (** Our final, successful, attempt uses an extra argument to [Hint Rewrite] that specifies a tactic to apply to generated premises.  Such a hint is only used when the tactic succeeds for all premises, possibly leaving further subgoals for some premises. *)

  Section garden_path.
    Variable P : A -> Prop.
    Variable g : A -> A.
    Hypothesis f_g : forall x, P x -> f x = g x.
(* begin thide *)
    Hint Rewrite f_g using assumption.
(* end thide *)

    Lemma f_f_f' : forall x, f (f (f x)) = f x.
(* begin thide *)
      intros; autorewrite with core; reflexivity.
    Qed.
(* end thide *)

    (** We may still use [autorewrite] to apply [f_g] when the generated premise is among our assumptions. *)

    Lemma f_f_f_g : forall x, P x -> f (f x) = g x.
(* begin thide *)
      intros; autorewrite with core; reflexivity.
(* end thide *)
    Qed.
  End garden_path.

  (** It can also be useful to apply the [autorewrite with db in *] form, which does rewriting in hypotheses, as well as in the conclusion. *)

  Lemma in_star : forall x y, f (f (f (f x))) = f (f y)
    -> f x = f (f (f y)).
(* begin thide *)
    intros; autorewrite with core in *; assumption.
(* end thide *)
  Qed.

End autorewrite.

(** Many proofs can be automated in pleasantly modular ways with deft combinations of [auto] and [autorewrite]. *)
