(* Copyright (c) 2008-2012, Adam Chlipala
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


(** %\part{Basic Programming and Proving}

\chapter{Introducing Inductive Types}% *)

(** The logical foundation of Coq is the Calculus of Inductive Constructions, or CIC.  In a sense, CIC is built from just two relatively straightforward features: function types and inductive types.  From this modest foundation, we can prove essentially all of the theorems of math and carry out effectively all program verifications, with enough effort expended.  This chapter introduces induction and recursion for functional programming in Coq.  Most of our examples reproduce functionality from the Coq standard library, and I have tried to copy the standard library's choices of identifiers, where possible, so many of the definitions here are already available in the default Coq environment.

The last chapter took a deep dive into some of the more advanced Coq features, to highlight the unusual approach that I advocate in this book.  However, from this point on, we will rewind and go back to basics, presenting the relevant features of Coq in a more bottom-up manner.  A useful first step is a discussion of the differences and relationships between proofs and programs in Coq. *)


(** * Proof Terms *)

(** Mainstream presentations of mathematics treat proofs as objects that exist outside of the universe of mathematical objects.  However, for a variety of reasoning tasks, it is convenient to encode proofs, traditional mathematical objects, and programs within a single formal language.  Validity checks on mathematical objects are useful in any setting, to catch typos and other uninteresting errors.  The benefits of static typing for programs are widely recognized, and Coq brings those benefits to both mathematical objects and programs via a uniform mechanism.  In fact, from this point on, we will not bother to distinguish between programs and mathematical objects.  Many mathematical formalisms are most easily encoded in terms of programs.

Proofs are fundamentally different from programs, because any two proofs of a theorem are considered equivalent, from a formal standpoint if not from an engineering standpoint.  However, we can use the same type-checking technology to check proofs as we use to validate our programs.  This is the%\index{Curry-Howard correspondence}% _Curry-Howard correspondence_ %\cite{Curry,Howard}%, an approach for relating proofs and programs.  We represent mathematical theorems as types, such that a theorem's proofs are exactly those programs that type-check at the corresponding type.

The last chapter's example already snuck in an instance of Curry-Howard.  We used the token [->] to stand for both function types and logical implications.  One reasonable conclusion upon seeing this might be that some fancy overloading of notations is at work.  In fact, functions and implications are precisely identical according to Curry-Howard!  That is, they are just two ways of describing the same computational phenomenon.

A short demonstration should explain how this can be.  The identity function over the natural numbers is certainly not a controversial program. *)

Check (fun x : nat => x).
(** [: nat -> nat] *)

(** %\smallskip{}%Consider this alternate program, which is almost identical to the last one. *)

Check (fun x : True => x).
(** [: True -> True] *)

(** %\smallskip{}%The identity program is interpreted as a proof that %\index{Gallina terms!True}%[True], the always-true proposition, implies itself!  What we see is that Curry-Howard interprets implications as functions, where an input is a proposition being assumed and an output is a proposition being deduced.  This intuition is not too far from a common one for informal theorem proving, where we might already think of an implication proof as a process for transforming a hypothesis into a conclusion.

There are also more primitive proof forms available.  For instance, the term %\index{Gallina terms!I}%[I] is the single proof of [True], applicable in any context. *)

Check I.
(** [: True] *)

(** %\smallskip{}%With [I], we can prove another simple propositional theorem. *)

Check (fun _ : False => I).
(** [: False -> True] *)

(** %\smallskip{}%No proofs of %\index{Gallina terms!False}%[False] exist in the top-level context, but the implication-as-function analogy gives us an easy way to, for example, show that [False] implies itself. *)

Check (fun x : False => x).
(** [: False -> False] *)

(** %\smallskip{}%Every one of these example programs whose type looks like a logical formula is a%\index{proof term}% _proof term_.  We use that name for any Gallina term of a logical type, and we will elaborate shortly on what makes a type logical.

In the rest of this chapter, we will introduce different ways of defining types.  Every example type can be interpreted alternatively as a type of programs or proofs.

One of the first types we introduce will be [bool], with constructors [true] and [false].  Newcomers to Coq often wonder about the distinction between [True] and [true] and the distinction between [False] and [false].  One glib answer is that [True] and [False] are types, but [true] and [false] are not.  A more useful answer is that Coq's metatheory guarantees that any term of type [bool] _evaluates_ to either [true] or [false].  This means that we have an _algorithm_ for answering any question phrased as an expression of type [bool].  Conversely, most propositions do not evaluate to [True] or [False]; the language of inductively defined propositions is much richer than that.  We ought to be glad that we have no algorithm for deciding our formalized version of mathematical truth, since otherwise it would be clear that we could not formalize undecidable properties, like almost any interesting property of general-purpose programs. *)


(** * Enumerations *)

(** Coq inductive types generalize the %\index{algebraic datatypes}%algebraic datatypes found in %\index{Haskell}%Haskell and %\index{ML}%ML.  Confusingly enough, inductive types also generalize %\index{generalized algebraic datatypes}%generalized algebraic datatypes (GADTs), by adding the possibility for type dependency.  Even so, it is worth backing up from the examples of the last chapter and going over basic, algebraic-datatype uses of inductive datatypes, because the chance to prove things about the values of these types adds new wrinkles beyond usual practice in Haskell and ML.

The singleton type [unit] is an inductive type:%\index{Gallina terms!unit}\index{Gallina terms!tt}% *)

Inductive unit : Set :=
  | tt.

(** This vernacular command defines a new inductive type [unit] whose only value is [tt].  We can verify the types of the two identifiers we introduce: *)

Check unit.
(** [unit : Set] *)

Check tt.
(** [tt : unit] *)

(** %\smallskip{}%We can prove that [unit] is a genuine singleton type. *)

Theorem unit_singleton : forall x : unit, x = tt.

(** The important thing about an inductive type is, unsurprisingly, that you can do induction over its values, and induction is the key to proving this theorem.  We ask to proceed by induction on the variable [x].%\index{tactics!induction}% *)

(* begin thide *)
  induction x.

(** The goal changes to:
[[
 tt = tt
]]
*)

  (** %\noindent{}%...which we can discharge trivially. *)

  reflexivity.
Qed.
(* end thide *)

(** It seems kind of odd to write a proof by induction with no inductive hypotheses.  We could have arrived at the same result by beginning the proof with:%\index{tactics!destruct}% [[
  destruct x.
]]

%\noindent%...which corresponds to "proof by case analysis" in classical math.  For non-recursive inductive types, the two tactics will always have identical behavior.  Often case analysis is sufficient, even in proofs about recursive types, and it is nice to avoid introducing unneeded induction hypotheses.

What exactly _is_ the %\index{induction principles}%induction principle for [unit]?  We can ask Coq: *)

Check unit_ind.
(** [unit_ind : forall P : unit -> Prop, P tt -> forall u : unit, P u] *)

(** %\smallskip{}%Every [Inductive] command defining a type [T] also defines an induction principle named [T_ind].  Recall from the last section that our type, operations over it, and principles for reasoning about it all live in the same language and are described by the same type system.  The key to telling what is a program and what is a proof lies in the distinction between the type %\index{Gallina terms!Prop}%[Prop], which appears in our induction principle; and the type %\index{Gallina terms!Set}%[Set], which we have seen a few times already.

The convention goes like this: [Set] is the type of normal types used in programming, and the values of such types are programs.  [Prop] is the type of logical propositions, and the values of such types are proofs.  Thus, an induction principle has a type that shows us that it is a function for building proofs.

Specifically, [unit_ind] quantifies over a predicate [P] over [unit] values.  If we can present a proof that [P] holds of [tt], then we are rewarded with a proof that [P] holds for any value [u] of type [unit].  In our last proof, the predicate was [(fun u : unit => u = tt)].

The definition of [unit] places the type in [Set].  By replacing [Set] with [Prop], [unit] with [True], and [tt] with [I], we arrive at precisely the definition of [True] that the Coq standard library employs!  The program type [unit] is the Curry-Howard equivalent of the proposition [True].  We might make the tongue-in-cheek claim that, while philosophers have expended much ink on the nature of truth, we have now determined that truth is the [unit] type of functional programming.

%\medskip%

We can define an inductive type even simpler than [unit]:%\index{Gallina terms!Empty\_set}% *)

Inductive Empty_set : Set := .

(** [Empty_set] has no elements.  We can prove fun theorems about it: *)

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
(* begin thide *)
  destruct 1.
Qed.
(* end thide *)

(** Because [Empty_set] has no elements, the fact of having an element of this type implies anything.  We use [destruct 1] instead of [destruct x] in the proof because unused quantified variables are relegated to being referred to by number.  (There is a good reason for this, related to the unity of quantifiers and implication.  At least within Coq's logical foundation of %\index{constructive logic}%constructive logic, which we elaborate on more in the next chapter, an implication is just a quantification over a proof, where the quantified variable is never used.  It generally makes more sense to refer to implication hypotheses by number than by name, and Coq treats our quantifier over an unused variable as an implication in determining the proper behavior.)

We can see the induction principle that made this proof so easy: *)

Check Empty_set_ind.
(** [Empty_set_ind : forall (P : Empty_set -> Prop) (e : Empty_set), P e] *)

(** %\smallskip{}%In other words, any predicate over values from the empty set holds vacuously of every such element.  In the last proof, we chose the predicate [(fun _ : Empty_set => 2 + 2 = 5)].

We can also apply this get-out-of-jail-free card programmatically.  Here is a lazy way of converting values of [Empty_set] to values of [unit]: *)

Definition e2u (e : Empty_set) : unit := match e with end.

(** We employ [match] pattern matching as in the last chapter.  Since we match on a value whose type has no constructors, there is no need to provide any branches.  It turns out that [Empty_set] is the Curry-Howard equivalent of [False].  As for why [Empty_set] starts with a capital letter and not a lowercase letter like [unit] does, we must refer the reader to the authors of the Coq standard library, to which we try to be faithful.

%\medskip%

Moving up the ladder of complexity, we can define the Booleans:%\index{Gallina terms!bool}\index{Gallina terms!true}\index{Gallina terms!false}% *)

Inductive bool : Set :=
| true
| false.

(** We can use less vacuous pattern matching to define Boolean negation.%\index{Gallina terms!negb}% *)

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

(** An alternative definition desugars to the above, thanks to an %\index{Gallina terms!if}%[if] notation overloaded to work with any inductive type that has exactly two constructors: *)

Definition negb' (b : bool) : bool :=
  if b then false else true.

(** We might want to prove that [negb] is its own inverse operation. *)

Theorem negb_inverse : forall b : bool, negb (negb b) = b.
(* begin thide *)
  destruct b.

  (** After we case-analyze on [b], we are left with one subgoal for each constructor of [bool].
[[
  2 subgoals

  ============================
   negb (negb true) = true

subgoal 2 is

 negb (negb false) = false
]]

The first subgoal follows by Coq's rules of computation, so we can dispatch it easily: *)

  reflexivity.

(** Likewise for the second subgoal, so we can restart the proof and give a very compact justification.%\index{Vernacular commands!Restart}% *)

Restart.

  destruct b; reflexivity.
Qed.
(* end thide *)

(** Another theorem about Booleans illustrates another useful tactic.%\index{tactics!discriminate}% *)

Theorem negb_ineq : forall b : bool, negb b <> b.
(* begin thide *)
  destruct b; discriminate.
Qed.
(* end thide *)

(** The [discriminate] tactic is used to prove that two values of an inductive type are not equal, whenever the values are formed with different constructors.  In this case, the different constructors are [true] and [false].

At this point, it is probably not hard to guess what the underlying induction principle for [bool] is. *)

Check bool_ind.
(** [bool_ind : forall P : bool -> Prop, P true -> P false -> forall b : bool, P b] *)

(** %\smallskip{}%That is, to prove that a property describes all [bool]s, prove that it describes both [true] and [false].

There is no interesting Curry-Howard analogue of [bool].  Of course, we can define such a type by replacing [Set] by [Prop] above, but the proposition we arrive at is not very useful.  It is logically equivalent to [True], but it provides two indistinguishable primitive proofs, [true] and [false].   In the rest of the chapter, we will skip commenting on Curry-Howard versions of inductive definitions where such versions are not interesting. *)


(** * Simple Recursive Types *)

(** The natural numbers are the simplest common example of an inductive type that actually deserves the name.%\index{Gallina terms!nat}\index{Gallina terms!O}\index{Gallina terms!S}% *)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(** The constructor [O] is zero, and [S] is the successor function, so that [0] is syntactic sugar for [O], [1] for [S O], [2] for [S (S O)], and so on.

Pattern matching works as we demonstrated in the last chapter:%\index{Gallina terms!pred}% *)

Definition isZero (n : nat) : bool :=
  match n with
    | O => true
    | S _ => false
  end.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

(** We can prove theorems by case analysis with [destruct] as for simpler inductive types, but we can also now get into genuine inductive theorems.  First, we will need a recursive function, to make things interesting.%\index{Gallina terms!plus}% *)

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

(** Recall that [Fixpoint] is Coq's mechanism for recursive function definitions.  Some theorems about [plus] can be proved without induction. *)

Theorem O_plus_n : forall n : nat, plus O n = n.
(* begin thide *)
  intro; reflexivity.
Qed.
(* end thide *)

(** Coq's computation rules automatically simplify the application of [plus], because unfolding the definition of [plus] gives us a [match] expression where the branch to be taken is obvious from syntax alone.  If we just reverse the order of the arguments, though, this no longer works, and we need induction. *)

Theorem n_plus_O : forall n : nat, plus n O = n.
(* begin thide *)
  induction n.

(** Our first subgoal is [plus O O = O], which _is_ trivial by computation. *)

  reflexivity.

(** Our second subgoal requires more work and also demonstrates our first inductive hypothesis.

[[
  n : nat
  IHn : plus n O = n
  ============================
   plus (S n) O = S n
 
]]

We can start out by using computation to simplify the goal as far as we can.%\index{tactics!simpl}% *)

  simpl.

(** Now the conclusion is [S (plus n O) = S n].  Using our inductive hypothesis: *)

  rewrite IHn.

(** %\noindent{}%...we get a trivial conclusion [S n = S n]. *)

  reflexivity.

(** Not much really went on in this proof, so the [crush] tactic from the [CpdtTactics] module can prove this theorem automatically. *)

Restart.

  induction n; crush.
Qed.
(* end thide *)

(** We can check out the induction principle at work here: *)

Check nat_ind.
(** %\vspace{-.15in}% [[
  nat_ind : forall P : nat -> Prop,
            P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
  ]]

Each of the two cases of our last proof came from the type of one of the arguments to [nat_ind].  We chose [P] to be [(fun n : nat => plus n O = n)].  The first proof case corresponded to [P O] and the second case to [(forall n : nat, P n -> P (S n))].  The free variable [n] and inductive hypothesis [IHn] came from the argument types given here.

Since [nat] has a constructor that takes an argument, we may sometimes need to know that that constructor is injective.%\index{tactics!injection}\index{tactics!trivial}% *)

Theorem S_inj : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  injection 1; trivial.
Qed.
(* end thide *)

(** The [injection] tactic refers to a premise by number, adding new equalities between the corresponding arguments of equated terms that are formed with the same constructor.  We end up needing to prove [n = m -> n = m], so it is unsurprising that a tactic named [trivial] is able to finish the proof.  This tactic attempts a variety of single proof steps, drawn from a user-specified database that we will later see how to extend.

There is also a very useful tactic called %\index{tactics!congruence}%[congruence] that can prove this theorem immediately.  The [congruence] tactic generalizes [discriminate] and [injection], and it also adds reasoning about the general properties of equality, such as that a function returns equal results on equal arguments.  That is, [congruence] is a%\index{theory of equality and uninterpreted functions}% _complete decision procedure for the theory of equality and uninterpreted functions_, plus some smarts about inductive types.

%\medskip%

We can define a type of lists of natural numbers. *)

Inductive nat_list : Set :=
| NNil : nat_list
| NCons : nat -> nat_list -> nat_list.

(** Recursive definitions over [nat_list] are straightforward extensions of what we have seen before. *)

Fixpoint nlength (ls : nat_list) : nat :=
  match ls with
    | NNil => O
    | NCons _ ls' => S (nlength ls')
  end.

Fixpoint napp (ls1 ls2 : nat_list) : nat_list :=
  match ls1 with
    | NNil => ls2
    | NCons n ls1' => NCons n (napp ls1' ls2)
  end.

(** Inductive theorem proving can again be automated quite effectively. *)

Theorem nlength_napp : forall ls1 ls2 : nat_list, nlength (napp ls1 ls2)
  = plus (nlength ls1) (nlength ls2).
(* begin thide *)
  induction ls1; crush.
Qed.
(* end thide *)

Check nat_list_ind.
(** %\vspace{-.15in}% [[
  nat_list_ind
     : forall P : nat_list -> Prop,
       P NNil ->
       (forall (n : nat) (n0 : nat_list), P n0 -> P (NCons n n0)) ->
       forall n : nat_list, P n
]]

%\medskip%

In general, we can implement any "tree" type as an inductive type.  For example, here are binary trees of naturals. *)

Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat_btree -> nat -> nat_btree -> nat_btree.

(** Here are two functions whose intuitive explanations are not so important.  The first one computes the size of a tree, and the second performs some sort of splicing of one tree into the leftmost available leaf node of another. *)

Fixpoint nsize (tr : nat_btree) : nat :=
  match tr with
    | NLeaf => S O
    | NNode tr1 _ tr2 => plus (nsize tr1) (nsize tr2)
  end.

Fixpoint nsplice (tr1 tr2 : nat_btree) : nat_btree :=
  match tr1 with
    | NLeaf => NNode tr2 O NLeaf
    | NNode tr1' n tr2' => NNode (nsplice tr1' tr2) n tr2'
  end.

Theorem plus_assoc : forall n1 n2 n3 : nat, plus (plus n1 n2) n3 = plus n1 (plus n2 n3).
(* begin thide *)
  induction n1; crush.
Qed.
(* end thide *)

Theorem nsize_nsplice : forall tr1 tr2 : nat_btree, nsize (nsplice tr1 tr2)
  = plus (nsize tr2) (nsize tr1).
(* begin thide *)
  Hint Rewrite n_plus_O plus_assoc.

  induction tr1; crush.
Qed.
(* end thide *)

(** It is convenient that these proofs go through so easily, but it is still useful to look into the details of what happened, by checking the statement of the tree induction principle. *)

Check nat_btree_ind.
(** %\vspace{-.15in}% [[
  nat_btree_ind
     : forall P : nat_btree -> Prop,
       P NLeaf ->
       (forall n : nat_btree,
        P n -> forall (n0 : nat) (n1 : nat_btree), P n1 -> P (NNode n n0 n1)) ->
       forall n : nat_btree, P n
]]

We have the usual two cases, one for each constructor of [nat_btree]. *)


(** * Parameterized Types *)

(** We can also define %\index{polymorphism}%polymorphic inductive types, as with algebraic datatypes in Haskell and ML.%\index{Gallina terms!list}\index{Gallina terms!Nil}\index{Gallina terms!Cons}\index{Gallina terms!length}\index{Gallina terms!app}% *)

Inductive list (T : Set) : Set :=
| Nil : list T
| Cons : T -> list T -> list T.

Fixpoint length T (ls : list T) : nat :=
  match ls with
    | Nil => O
    | Cons _ ls' => S (length ls')
  end.

Fixpoint app T (ls1 ls2 : list T) : list T :=
  match ls1 with
    | Nil => ls2
    | Cons x ls1' => Cons x (app ls1' ls2)
  end.

Theorem length_app : forall T (ls1 ls2 : list T), length (app ls1 ls2)
  = plus (length ls1) (length ls2).
(* begin thide *)
  induction ls1; crush.
Qed.
(* end thide *)

(** There is a useful shorthand for writing many definitions that share the same parameter, based on Coq's%\index{sections}\index{Vernacular commands!Section}\index{Vernacular commands!Variable}% _section_ mechanism.  The following block of code is equivalent to the above: *)

(* begin hide *)
Reset list.
(* end hide *)

Section list.
  Variable T : Set.

  Inductive list : Set :=
  | Nil : list
  | Cons : T -> list -> list.

  Fixpoint length (ls : list) : nat :=
    match ls with
      | Nil => O
      | Cons _ ls' => S (length ls')
    end.

  Fixpoint app (ls1 ls2 : list) : list :=
    match ls1 with
      | Nil => ls2
      | Cons x ls1' => Cons x (app ls1' ls2)
    end.

  Theorem length_app : forall ls1 ls2 : list, length (app ls1 ls2)
    = plus (length ls1) (length ls2).
(* begin thide *)
    induction ls1; crush.
  Qed.
(* end thide *)
End list.

Implicit Arguments Nil [T].

(** After we end the section, the [Variable]s we used are added as extra function parameters for each defined identifier, as needed.  With an [Implicit Arguments]%~\index{Vernacular commands!Implicit Arguments}% command, we ask that [T] be inferred when we use [Nil]; Coq's heuristics already decided to apply a similar policy to [Cons], because of the [Set Implicit Arguments]%~\index{Vernacular commands!Set Implicit Arguments}% command elided at the beginning of this chapter.  We verify that our definitions have been saved properly using the [Print] command, a cousin of [Check] which shows the definition of a symbol, rather than just its type. *)

Print list.
(** %\vspace{-.15in}% [[
  Inductive list (T : Set) : Set :=
    Nil : list T | Cons : T -> list T -> list T
]]

The final definition is the same as what we wrote manually before.  The other elements of the section are altered similarly, turning out exactly as they were before, though we managed to write their definitions more succinctly. *)

Check length.
(** %\vspace{-.15in}% [[
  length
     : forall T : Set, list T -> nat
]]

The parameter [T] is treated as a new argument to the induction principle, too. *)

Check list_ind.
(** %\vspace{-.15in}% [[
  list_ind
     : forall (T : Set) (P : list T -> Prop),
       P (Nil T) ->
       (forall (t : T) (l : list T), P l -> P (Cons t l)) ->
       forall l : list T, P l
]]

Thus, despite a very real sense in which the type [T] is an argument to the constructor [Cons], the inductive case in the type of [list_ind] (i.e., the third line of the type) includes no quantifier for [T], even though all of the other arguments are quantified explicitly.  Parameters in other inductive definitions are treated similarly in stating induction principles. *)


(** * Mutually Inductive Types *)

(** We can define inductive types that refer to each other: *)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list.

Fixpoint elength (el : even_list) : nat :=
  match el with
    | ENil => O
    | ECons _ ol => S (olength ol)
  end

with olength (ol : odd_list) : nat :=
  match ol with
    | OCons _ el => S (elength el)
  end.

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
    | ENil => el2
    | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
    | OCons n el' => OCons n (eapp el' el)
  end.

(** Everything is going roughly the same as in past examples, until we try to prove a theorem similar to those that came before. *)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).
(* begin thide *)
  induction el1; crush.

  (** One goal remains: [[

  n : nat
  o : odd_list
  el2 : even_list
  ============================
   S (olength (oapp o el2)) = S (plus (olength o) (elength el2))
   ]]

   We have no induction hypothesis, so we cannot prove this goal without starting another induction, which would reach a similar point, sending us into a futile infinite chain of inductions.  The problem is that Coq's generation of [T_ind] principles is incomplete.  We only get non-mutual induction principles generated by default. *)

Abort.
Check even_list_ind.
(** %\vspace{-.15in}% [[
  even_list_ind
     : forall P : even_list -> Prop,
       P ENil ->
       (forall (n : nat) (o : odd_list), P (ECons n o)) ->
       forall e : even_list, P e
]]

We see that no inductive hypotheses are included anywhere in the type.  To get them, we must ask for mutual principles as we need them, using the %\index{Vernacular commands!Scheme}%[Scheme] command. *)

Scheme even_list_mut := Induction for even_list Sort Prop
with odd_list_mut := Induction for odd_list Sort Prop.

(** This invocation of [Scheme] asks for the creation of induction principles [even_list_mut] for the type [even_list] and [odd_list_mut] for the type [odd_list].  The [Induction] keyword says we want standard induction schemes, since [Scheme] supports more exotic choices.  Finally, [Sort Prop] establishes that we really want induction schemes, not recursion schemes, which are the same according to Curry-Howard, save for the [Prop]/[Set] distinction. *)

Check even_list_mut.
(** %\vspace{-.15in}% [[
  even_list_mut
     : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
       P ENil ->
       (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
       (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
       forall e : even_list, P e
]]

This is the principle we wanted in the first place.

The [Scheme] command is for asking Coq to generate particular induction schemes that are mutual among a set of inductive types (possibly only one such type, in which case we get a normal induction principle).  In a sense, it generalizes the induction scheme generation that goes on automatically for each inductive definition.  Future Coq versions might make that automatic generation smarter, so that [Scheme] is needed in fewer places.  In a few sections, we will see how induction principles are derived theorems in Coq, so that there is not actually any need to build in _any_ automatic scheme generation.

There is one more wrinkle left in using the [even_list_mut] induction principle: the [induction] tactic will not apply it for us automatically.  It will be helpful to look at how to prove one of our past examples without using [induction], so that we can then generalize the technique to mutual inductive types.%\index{tactics!apply}% *)

Theorem n_plus_O' : forall n : nat, plus n O = n.
  apply nat_ind.
  (** Here we use [apply], which is one of the most essential basic tactics.  When we are trying to prove fact [P], and when [thm] is a theorem whose conclusion can be made to match [P] by proper choice of quantified variable values, the invocation [apply thm] will replace the current goal with one new goal for each premise of [thm].

     This use of [apply] may seem a bit _too_ magical.  To better see what is going on, we use a variant where we partially apply the theorem [nat_ind] to give an explicit value for the predicate that gives our induction hypothesis. *)

  Undo.
  apply (nat_ind (fun n => plus n O = n)); crush.
Qed.

(** From this example, we can see that [induction] is not magic.  It only does some bookkeeping for us to make it easy to apply a theorem, which we can do directly with the [apply] tactic.

This technique generalizes to our mutual example: *)

Theorem elength_eapp : forall el1 el2 : even_list,
  elength (eapp el1 el2) = plus (elength el1) (elength el2).

  apply (even_list_mut
    (fun el1 : even_list => forall el2 : even_list,
      elength (eapp el1 el2) = plus (elength el1) (elength el2))
    (fun ol : odd_list => forall el : even_list,
      olength (oapp ol el) = plus (olength ol) (elength el))); crush.
Qed.
(* end thide *)

(** We simply need to specify two predicates, one for each of the mutually inductive types.  In general, it is not a good idea to assume that a proof assistant can infer extra predicates, so this way of applying mutual induction is about as straightforward as we may hope for. *)


(** * Reflexive Types *)

(** A kind of inductive type called a _reflexive type_ includes at least one constructor that takes as an argument _a function returning the same type we are defining_.  One very useful class of examples is in modeling variable binders.  Our example will be an encoding of the syntax of first-order logic.  Since the idea of syntactic encodings of logic may require a bit of acclimation, let us first consider a simpler formula type for a subset of propositional logic.  We are not yet using a reflexive type, but later we will extend the example reflexively. *)

Inductive pformula : Set :=
| Truth : pformula
| Falsehood : pformula
| Conjunction : pformula -> pformula -> pformula.

(* begin hide *)
(* begin thide *)
Definition prod' := prod.
(* end thide *)
(* end hide *)

(** A key distinction here is between, for instance, the _syntax_ [Truth] and its _semantics_ [True].  We can make the semantics explicit with a recursive function.  This function uses the infix operator %\index{Gallina operators!/\textbackslash}%[/\], which desugars to instances of the type family %\index{Gallina terms!and}%[and] from the standard library.  The family [and] implements conjunction, the [Prop] Curry-Howard analogue of the usual pair type from functional programming (which is the type family %\index{Gallina terms!prod}%[prod] in Coq's standard library). *)

Fixpoint pformulaDenote (f : pformula) : Prop :=
  match f with
    | Truth => True
    | Falsehood => False
    | Conjunction f1 f2 => pformulaDenote f1 /\ pformulaDenote f2
  end.

(** This is just a warm-up that does not use reflexive types, the new feature we mean to introduce.  When we set our sights on first-order logic instead, it becomes very handy to give constructors recursive arguments that are functions. *)

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula.

(** Our kinds of formulas are equalities between naturals, conjunction, and universal quantification over natural numbers.  We avoid needing to include a notion of "variables" in our type, by using Coq functions to encode the syntax of quantification.  For instance, here is the encoding of [forall x : nat, x = x]:%\index{Vernacular commands!Example}% *)

Example forall_refl : formula := Forall (fun x => Eq x x).

(** We can write recursive functions over reflexive types quite naturally.  Here is one translating our formulas into native Coq propositions. *)

Fixpoint formulaDenote (f : formula) : Prop :=
  match f with
    | Eq n1 n2 => n1 = n2
    | And f1 f2 => formulaDenote f1 /\ formulaDenote f2
    | Forall f' => forall n : nat, formulaDenote (f' n)
  end.

(** We can also encode a trivial formula transformation that swaps the order of equality and conjunction operands. *)

Fixpoint swapper (f : formula) : formula :=
  match f with
    | Eq n1 n2 => Eq n2 n1
    | And f1 f2 => And (swapper f2) (swapper f1)
    | Forall f' => Forall (fun n => swapper (f' n))
  end.

(** It is helpful to prove that this transformation does not make true formulas false. *)

Theorem swapper_preserves_truth : forall f, formulaDenote f -> formulaDenote (swapper f).
(* begin thide *)
  induction f; crush.
Qed.
(* end thide *)

(** We can take a look at the induction principle behind this proof. *)

Check formula_ind.
(** %\vspace{-.15in}% [[
  formula_ind
     : forall P : formula -> Prop,
       (forall n n0 : nat, P (Eq n n0)) ->
       (forall f0 : formula,
        P f0 -> forall f1 : formula, P f1 -> P (And f0 f1)) ->
       (forall f1 : nat -> formula,
        (forall n : nat, P (f1 n)) -> P (Forall f1)) ->
       forall f2 : formula, P f2
]]

Focusing on the [Forall] case, which comes third, we see that we are allowed to assume that the theorem holds _for any application of the argument function [f1]_.  That is, Coq induction principles do not follow a simple rule that the textual representations of induction variables must get shorter in appeals to induction hypotheses.  Luckily for us, the people behind the metatheory of Coq have verified that this flexibility does not introduce unsoundness.

%\medskip%

Up to this point, we have seen how to encode in Coq more and more of what is possible with algebraic datatypes in %\index{Haskell}%Haskell and %\index{ML}%ML.  This may have given the inaccurate impression that inductive types are a strict extension of algebraic datatypes.  In fact, Coq must rule out some types allowed by Haskell and ML, for reasons of soundness.  Reflexive types provide our first good example of such a case; only some of them are legal.

Given our last example of an inductive type, many readers are probably eager to try encoding the syntax of %\index{lambda calculus}%lambda calculus.  Indeed, the function-based representation technique that we just used, called%\index{higher-order abstract syntax}\index{HOAS|see{higher-order abstract syntax}}% _higher-order abstract syntax_ (HOAS)%~\cite{HOAS}%, is the representation of choice for lambda calculi in %\index{Twelf}%Twelf and in many applications implemented in Haskell and ML.  Let us try to import that choice to Coq: *)
(* begin hide *)
(* begin thide *)
Inductive term : Set := App | Abs.
Reset term.
Definition uhoh := O.
(* end thide *)
(* end hide *)
(** [[
Inductive term : Set :=
| App : term -> term -> term
| Abs : (term -> term) -> term.
]]

<<
Error: Non strictly positive occurrence of "term" in "(term -> term) -> term"
>>

We have run afoul of the%\index{strict positivity requirement}\index{positivity requirement}% _strict positivity requirement_ for inductive definitions, which says that the type being defined may not occur to the left of an arrow in the type of a constructor argument.  It is important that the type of a constructor is viewed in terms of a series of arguments and a result, since obviously we need recursive occurrences to the lefts of the outermost arrows if we are to have recursive occurrences at all.  Our candidate definition above violates the positivity requirement because it involves an argument of type [term -> term], where the type [term] that we are defining appears to the left of an arrow.  The candidate type of [App] is fine, however, since every occurrence of [term] is either a constructor argument or the final result type.

Why must Coq enforce this restriction?  Imagine that our last definition had been accepted, allowing us to write this function:

%\vspace{-.15in}%[[
Definition uhoh (t : term) : term :=
  match t with
    | Abs f => f t
    | _ => t
  end.
]]

Using an informal idea of Coq's semantics, it is easy to verify that the application [uhoh (Abs uhoh)] will run forever.  This would be a mere curiosity in OCaml and Haskell, where non-termination is commonplace, though the fact that we have a non-terminating program without explicit recursive function definitions is unusual.

%\index{termination checking}%For Coq, however, this would be a disaster.  The possibility of writing such a function would destroy all our confidence that proving a theorem means anything.  Since Coq combines programs and proofs in one language, we would be able to prove every theorem with an infinite loop.

Nonetheless, the basic insight of HOAS is a very useful one, and there are ways to realize most benefits of HOAS in Coq.  We will study a particular technique of this kind in the final chapter, on programming language syntax and semantics. *)


(** * An Interlude on Induction Principles *)

(** As we have emphasized a few times already, Coq proofs are actually programs, written in the same language we have been using in our examples all along.  We can get a first sense of what this means by taking a look at the definitions of some of the %\index{induction principles}%induction principles we have used.  A close look at the details here will help us construct induction principles manually, which we will see is necessary for some more advanced inductive definitions. *)

Print nat_ind.
(** %\vspace{-.15in}%[[
nat_ind = 
fun P : nat -> Prop => nat_rect P
     : forall P : nat -> Prop,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

We see that this induction principle is defined in terms of a more general principle, [nat_rect].  The <<rec>> stands for "recursion principle," and the <<t>> at the end stands for [Type]. *)

Check nat_rect.
(** %\vspace{-.15in}% [[
nat_rect
     : forall P : nat -> Type,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

The principle [nat_rect] gives [P] type [nat -> Type] instead of [nat -> Prop].  This [Type] is another universe, like [Set] and [Prop].  In fact, it is a common supertype of both.  Later on, we will discuss exactly what the significances of the different universes are.  For now, it is just important that we can use [Type] as a sort of meta-universe that may turn out to be either [Set] or [Prop].  We can see the symmetry inherent in the subtyping relationship by printing the definition of another principle that was generated for [nat] automatically: *)

Print nat_rec.
(** %\vspace{-.15in}%[[
nat_rec = 
fun P : nat -> Set => nat_rect P
     : forall P : nat -> Set,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

This is identical to the definition for [nat_ind], except that we have substituted [Set] for [Prop].  For most inductive types [T], then, we get not just induction principles [T_ind], but also %\index{recursion principles}%recursion principles [T_rec].  We can use [T_rec] to write recursive definitions without explicit [Fixpoint] recursion.  For instance, the following two definitions are equivalent: *)

Fixpoint plus_recursive (n : nat) : nat -> nat :=
  match n with
    | O => fun m => m
    | S n' => fun m => S (plus_recursive n' m)
  end.

Definition plus_rec : nat -> nat -> nat :=
  nat_rec (fun _ : nat => nat -> nat) (fun m => m) (fun _ r m => S (r m)).

Theorem plus_equivalent : plus_recursive = plus_rec.
  reflexivity.
Qed.

(** Going even further down the rabbit hole, [nat_rect] itself is not even a primitive.  It is a functional program that we can write manually. *)

Print nat_rect.
(** %\vspace{-.15in}%[[
nat_rect = 
fun (P : nat -> Type) (f : P O) (f0 : forall n : nat, P n -> P (S n)) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | O => f
  | S n0 => f0 n0 (F n0)
  end
     : forall P : nat -> Type,
       P O -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
]]

The only new wrinkles here are, first, an anonymous recursive function definition, using the %\index{Gallina terms!fix}%[fix] keyword of Gallina (which is like [fun] with recursion supported); and, second, the annotations on the [match] expression.  This is a%\index{dependent pattern matching}% _dependently typed_ pattern match, because the _type_ of the expression depends on the _value_ being matched on.  We will meet more involved examples later, especially in Part II of the book.

%\index{type inference}%Type inference for dependent pattern matching is undecidable, which can be proved by reduction from %\index{higher-order unification}%higher-order unification%~\cite{HOU}%.  Thus, we often find ourselves needing to annotate our programs in a way that explains dependencies to the type checker.  In the example of [nat_rect], we have an %\index{Gallina terms!as}%[as] clause, which binds a name for the discriminee; and a %\index{Gallina terms!return}%[return] clause, which gives a way to compute the [match] result type as a function of the discriminee.

To prove that [nat_rect] is nothing special, we can reimplement it manually. *)

Fixpoint nat_rect' (P : nat -> Type) 
  (HO : P O)
  (HS : forall n, P n -> P (S n)) (n : nat) :=
  match n return P n with
    | O => HO
    | S n' => HS n' (nat_rect' P HO HS n')
  end.

(** We can understand the definition of [nat_rect] better by reimplementing [nat_ind] using sections. *)

Section nat_ind'.
   (** First, we have the property of natural numbers that we aim to prove. *)

  Variable P : nat -> Prop.

   (** Then we require a proof of the [O] case, which we declare with the command %\index{Vernacular commands!Hypothesis}%[Hypothesis], which is a synonym for [Variable] that, by convention, is used for variables whose types are propositions. *)

  Hypothesis O_case : P O.

   (** Next is a proof of the [S] case, which may assume an inductive hypothesis. *)

  Hypothesis S_case : forall n : nat, P n -> P (S n).

   (** Finally, we define a recursive function to tie the pieces together. *)

  Fixpoint nat_ind' (n : nat) : P n :=
    match n with
      | O => O_case
      | S n' => S_case (nat_ind' n')
    end.
End nat_ind'.

(** Closing the section adds the [Variable]s and [Hypothesis]es as new [fun]-bound arguments to [nat_ind'], and, modulo the use of [Prop] instead of [Type], we end up with the exact same definition that was generated automatically for [nat_rect].

%\medskip%

We can also examine the definition of [even_list_mut], which we generated with [Scheme] for a mutually recursive type. *)

Print even_list_mut.
(** %\vspace{-.15in}%[[
  even_list_mut = 
  fun (P : even_list -> Prop) (P0 : odd_list -> Prop) 
    (f : P ENil) (f0 : forall (n : nat) (o : odd_list), P0 o -> P (ECons n o))
    (f1 : forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) =>
  fix F (e : even_list) : P e :=
    match e as e0 return (P e0) with
    | ENil => f
    | ECons n o => f0 n o (F0 o)
    end
  with F0 (o : odd_list) : P0 o :=
    match o as o0 return (P0 o0) with
    | OCons n e => f1 n e (F e)
    end
  for F
     : forall (P : even_list -> Prop) (P0 : odd_list -> Prop),
       P ENil ->
       (forall (n : nat) (o : odd_list), P0 o -> P (ECons n o)) ->
       (forall (n : nat) (e : even_list), P e -> P0 (OCons n e)) ->
       forall e : even_list, P e
]]

We see a mutually recursive [fix], with the different functions separated by %\index{Gallina terms!with}%[with] in the same way that they would be separated by <<and>> in ML.  A final %\index{Gallina terms!for}%[for] clause identifies which of the mutually recursive functions should be the final value of the [fix] expression.  Using this definition as a template, we can reimplement [even_list_mut] directly. *)

Section even_list_mut'.
  (** First, we need the properties that we are proving. *)

  Variable Peven : even_list -> Prop.
  Variable Podd : odd_list -> Prop.

  (** Next, we need proofs of the three cases. *)

  Hypothesis ENil_case : Peven ENil.
  Hypothesis ECons_case : forall (n : nat) (o : odd_list), Podd o -> Peven (ECons n o).
  Hypothesis OCons_case : forall (n : nat) (e : even_list), Peven e -> Podd (OCons n e).

  (** Finally, we define the recursive functions. *)

  Fixpoint even_list_mut' (e : even_list) : Peven e :=
    match e with
      | ENil => ENil_case
      | ECons n o => ECons_case n (odd_list_mut' o)
    end
  with odd_list_mut' (o : odd_list) : Podd o :=
    match o with
      | OCons n e => OCons_case n (even_list_mut' e)
    end.
End even_list_mut'.

(** Even induction principles for reflexive types are easy to implement directly.  For our [formula] type, we can use a recursive definition much like those we wrote above. *)

Section formula_ind'.
  Variable P : formula -> Prop.
  Hypothesis Eq_case : forall n1 n2 : nat, P (Eq n1 n2).
  Hypothesis And_case : forall f1 f2 : formula,
    P f1 -> P f2 -> P (And f1 f2).
  Hypothesis Forall_case : forall f : nat -> formula,
    (forall n : nat, P (f n)) -> P (Forall f).

  Fixpoint formula_ind' (f : formula) : P f :=
    match f with
      | Eq n1 n2 => Eq_case n1 n2
      | And f1 f2 => And_case (formula_ind' f1) (formula_ind' f2)
      | Forall f' => Forall_case f' (fun n => formula_ind' (f' n))
    end.
End formula_ind'.

(** It is apparent that induction principle implementations involve some tedium but not terribly much creativity. *)


(** * Nested Inductive Types *)

(** Suppose we want to extend our earlier type of binary trees to trees with arbitrary finite branching.  We can use lists to give a simple definition. *)

Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree.

(** This is an example of a%\index{nested inductive type}% _nested_ inductive type definition, because we use the type we are defining as an argument to a parameterized type family.  Coq will not allow all such definitions; it effectively pretends that we are defining [nat_tree] mutually with a version of [list] specialized to [nat_tree], checking that the resulting expanded definition satisfies the usual rules.  For instance, if we replaced [list] with a type family that used its parameter as a function argument, then the definition would be rejected as violating the positivity restriction.

As we encountered with mutual inductive types, we find that the automatically generated induction principle for [nat_tree] is too weak. *)

(* begin hide *)
(* begin thide *)
Check Forall.
(* end thide *)
(* end hide *)

Check nat_tree_ind.
(** %\vspace{-.15in}% [[
  nat_tree_ind
     : forall P : nat_tree -> Prop,
       (forall (n : nat) (l : list nat_tree), P (NNode' n l)) ->
       forall n : nat_tree, P n
]]

There is no command like [Scheme] that will implement an improved principle for us.  In general, it takes creativity to figure out _good_ ways to incorporate nested uses of different type families.  Now that we know how to implement induction principles manually, we are in a position to apply just such creativity to this problem.

Many induction principles for types with nested used of [list] could benefit from a unified predicate capturing the idea that some property holds of every element in a list.  By defining this generic predicate once, we facilitate reuse of library theorems about it.  (Here, we are actually duplicating the standard library's [Forall] predicate, with a different implementation, for didactic purposes.) *)

Section All.
  Variable T : Set.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | Nil => True
      | Cons h t => P h /\ All t
    end.
End All.

(** It will be useful to review the definitions of [True] and [/\], since we will want to write manual proofs of them below. *)

Print True.
(** %\vspace{-.15in}%[[
  Inductive True : Prop :=  I : True
  ]]

That is, [True] is a proposition with exactly one proof, [I], which we may always supply trivially.

Finding the definition of [/\] takes a little more work.  Coq supports user registration of arbitrary parsing rules, and it is such a rule that is letting us write [/\] instead of an application of some inductive type family.  We can find the underlying inductive type with the %\index{Vernacular commands!Locate}%[Locate] command, whose argument may be a parsing token.%\index{Gallina terms!and}% *)

Locate "/\".
(** %\vspace{-.15in}%[[
  "A /\ B" := and A B  : type_scope (default interpretation)
]]
*)

Print and.
(** %\vspace{-.15in}%[[
  Inductive and (A : Prop) (B : Prop) : Prop :=  conj : A -> B -> A /\ B
]]
%\vspace{-.1in}%
<<
  For conj: Arguments A, B are implicit
>>

In addition to the definition of [and] itself, we get information on %\index{implicit arguments}%implicit arguments (and some other information that we omit here).  The implicit argument information tells us that we build a proof of a conjunction by calling the constructor [conj] on proofs of the conjuncts, with no need to include the types of those proofs as explicit arguments.

%\medskip%

Now we create a section for our induction principle, following the same basic plan as in the previous section of this chapter. *)

Section nat_tree_ind'.
  Variable P : nat_tree -> Prop.

  Hypothesis NNode'_case : forall (n : nat) (ls : list nat_tree),
    All P ls -> P (NNode' n ls).

  (* begin hide *)
  (* begin thide *)
  Definition list_nat_tree_ind := O.
  (* end thide *)
  (* end hide *)

  (** A first attempt at writing the induction principle itself follows the intuition that nested inductive type definitions are expanded into mutual inductive definitions.

  %\vspace{-.15in}%[[
  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls (list_nat_tree_ind ls)
    end

  with list_nat_tree_ind (ls : list nat_tree) : All P ls :=
    match ls with
      | Nil => I
      | Cons tr rest => conj (nat_tree_ind' tr) (list_nat_tree_ind rest)
    end.
  ]]

  Coq rejects this definition, saying
<<
  Recursive call to nat_tree_ind' has principal argument equal to "tr"
  instead of rest.
>>

  There is no deep theoretical reason why this program should be rejected; Coq applies incomplete termination-checking heuristics, and it is necessary to learn a few of the most important rules.  The term "nested inductive type" hints at the solution to this particular problem.  Just as mutually inductive types require mutually recursive induction principles, nested types require nested recursion. *)

  Fixpoint nat_tree_ind' (tr : nat_tree) : P tr :=
    match tr with
      | NNode' n ls => NNode'_case n ls
        ((fix list_nat_tree_ind (ls : list nat_tree) : All P ls :=
          match ls with
            | Nil => I
            | Cons tr' rest => conj (nat_tree_ind' tr') (list_nat_tree_ind rest)
          end) ls)
    end.

  (** We include an anonymous [fix] version of [list_nat_tree_ind] that is literally _nested_ inside the definition of the recursive function corresponding to the inductive definition that had the nested use of [list].   *)

End nat_tree_ind'.

(** We can try our induction principle out by defining some recursive functions on [nat_tree] and proving a theorem about them.  First, we define some helper functions that operate on lists. *)

Section map.
  Variables T T' : Set.
  Variable F : T -> T'.

  Fixpoint map (ls : list T) : list T' :=
    match ls with
      | Nil => Nil
      | Cons h t => Cons (F h) (map t)
    end.
End map.

Fixpoint sum (ls : list nat) : nat :=
  match ls with
    | Nil => O
    | Cons h t => plus h (sum t)
  end.

(** Now we can define a size function over our trees. *)

Fixpoint ntsize (tr : nat_tree) : nat :=
  match tr with
    | NNode' _ trs => S (sum (map ntsize trs))
  end.

(** Notice that Coq was smart enough to expand the definition of [map] to verify that we are using proper nested recursion, even through a use of a higher-order function. *)

Fixpoint ntsplice (tr1 tr2 : nat_tree) : nat_tree :=
  match tr1 with
    | NNode' n Nil => NNode' n (Cons tr2 Nil)
    | NNode' n (Cons tr trs) => NNode' n (Cons (ntsplice tr tr2) trs)
  end.

(** We have defined another arbitrary notion of tree splicing, similar to before, and we can prove an analogous theorem about its relationship with tree size.  We start with a useful lemma about addition. *)

(* begin thide *)
Lemma plus_S : forall n1 n2 : nat,
  plus n1 (S n2) = S (plus n1 n2).
  induction n1; crush.
Qed.
(* end thide *)

(** Now we begin the proof of the theorem, adding the lemma [plus_S] as a hint. *)

Theorem ntsize_ntsplice : forall tr1 tr2 : nat_tree, ntsize (ntsplice tr1 tr2)
  = plus (ntsize tr2) (ntsize tr1).
(* begin thide *)
  Hint Rewrite plus_S.

  (** We know that the standard induction principle is insufficient for the task, so we need to provide a %\index{tactics!using}%[using] clause for the [induction] tactic to specify our alternate principle. *)

  induction tr1 using nat_tree_ind'; crush.

  (** One subgoal remains: [[
  n : nat
  ls : list nat_tree
  H : All
        (fun tr1 : nat_tree =>
         forall tr2 : nat_tree,
         ntsize (ntsplice tr1 tr2) = plus (ntsize tr2) (ntsize tr1)) ls
  tr2 : nat_tree
  ============================
   ntsize
     match ls with
     | Nil => NNode' n (Cons tr2 Nil)
     | Cons tr trs => NNode' n (Cons (ntsplice tr tr2) trs)
     end = S (plus (ntsize tr2) (sum (map ntsize ls)))
 
     ]]

     After a few moments of squinting at this goal, it becomes apparent that we need to do a case analysis on the structure of [ls].  The rest is routine. *)

  destruct ls; crush.

  (** We can go further in automating the proof by exploiting the hint mechanism.%\index{Vernacular commands!Hint Extern}% *)

  Restart.

  Hint Extern 1 (ntsize (match ?LS with Nil => _ | Cons _ _ => _ end) = _) =>
    destruct LS; crush.
  induction tr1 using nat_tree_ind'; crush.
Qed.
(* end thide *)

(** We will go into great detail on hints in a later chapter, but the only important thing to note here is that we register a pattern that describes a conclusion we expect to encounter during the proof.  The pattern may contain unification variables, whose names are prefixed with question marks, and we may refer to those bound variables in a tactic that we ask to have run whenever the pattern matches.

The advantage of using the hint is not very clear here, because the original proof was so short.  However, the hint has fundamentally improved the readability of our proof.  Before, the proof referred to the local variable [ls], which has an automatically generated name.  To a human reading the proof script without stepping through it interactively, it was not clear where [ls] came from.  The hint explains to the reader the process for choosing which variables to case analyze, and the hint can continue working even if the rest of the proof structure changes significantly. *)


(** * Manual Proofs About Constructors *)

(** It can be useful to understand how tactics like %\index{tactics!discriminate}%[discriminate] and %\index{tactics!injection}%[injection] work, so it is worth stepping through a manual proof of each kind.  We will start with a proof fit for [discriminate]. *)

Theorem true_neq_false : true <> false.

(* begin thide *)
(** We begin with the tactic %\index{tactics!red}%[red], which is short for "one step of reduction," to unfold the definition of logical negation. *)

  red.
(** %\vspace{-.15in}%[[
  ============================
   true = false -> False
]]

The negation is replaced with an implication of falsehood.  We use the tactic %\index{tactics!intro}%[intro H] to change the assumption of the implication into a hypothesis named [H]. *)

  intro H.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   False
]]

This is the point in the proof where we apply some creativity.  We define a function whose utility will become clear soon. *)

  Definition toProp (b : bool) := if b then True else False.

(** It is worth recalling the difference between the lowercase and uppercase versions of truth and falsehood: [True] and [False] are logical propositions, while [true] and [false] are Boolean values that we can case-analyze.  We have defined [toProp] such that our conclusion of [False] is computationally equivalent to [toProp false].  Thus, the %\index{tactics!change}%[change] tactic will let us change the conclusion to [toProp false].  The general form [change e] replaces the conclusion with [e], whenever Coq's built-in computation rules suffice to establish the equivalence of [e] with the original conclusion. *)

  change (toProp false).
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   toProp false
]]

Now the righthand side of [H]'s equality appears in the conclusion, so we can rewrite, using the notation [<-] to request to replace the righthand side of the equality with the lefthand side.%\index{tactics!rewrite}% *)

  rewrite <- H.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   toProp true
]]

We are almost done.  Just how close we are to done is revealed by computational simplification. *)

  simpl.
(** %\vspace{-.15in}%[[
  H : true = false
  ============================
   True
]]
*)

  trivial.
Qed.
(* end thide *)

(** I have no trivial automated version of this proof to suggest, beyond using [discriminate] or [congruence] in the first place.

%\medskip%

We can perform a similar manual proof of injectivity of the constructor [S].  I leave a walk-through of the details to curious readers who want to run the proof script interactively. *)

Theorem S_inj' : forall n m : nat, S n = S m -> n = m.
(* begin thide *)
  intros n m H.
  change (pred (S n) = pred (S m)).
  rewrite H.
  reflexivity.
Qed.
(* end thide *)

(** The key piece of creativity in this theorem comes in the use of the natural number predecessor function [pred].  Embodied in the implementation of [injection] is a generic recipe for writing such type-specific functions.

The examples in this section illustrate an important aspect of the design philosophy behind Coq.  We could certainly design a Gallina replacement that built in rules for constructor discrimination and injectivity, but a simpler alternative is to include a few carefully chosen rules that enable the desired reasoning patterns and many others.  A key benefit of this philosophy is that the complexity of proof checking is minimized, which bolsters our confidence that proved theorems are really true. *)
