#lang scribble/base
@(require "util.rkt" "cite.rkt")

@title[#:tag "sec:insert"]{Introducing Our Library: Braun Tree Insert}

The core of our library is a monad that, as part of
its types, tracks the running time of functions.
To use the library, programs must be written using
the usual return and bind monadic operations. In return,
the result type of a function can use not only the argument
values to give it a very precise specification, but the
type also has access to an abstract step count describing
how many primitive operations the function executes.

To see how this works,
we start with a definition of Braun trees@~cite[Braun]
and the insertion function where the running time
for the function is declared as part of the body of the function.
In the next section, we make the running times implicit. 

Braun trees are a form of balanced binary trees 
where the balance condition allows only a single shape of
trees for a given size. Specifically, for each interior
node, either the two children are exactly the same size or
the left child's size is one larger than the right child's
size.

Because this invariant is so strong, explicit balance
information is not needed in the data structure that
represents Braun trees; we can use a simple binary tree
definition.

@(apply inline-code (extract braun.v "bin_tree"))

To be able to state facts about Braun trees, however,
we use @tt{Braun} to define when a binary tree is a
Braun tree of size @tt{n} (much like our definition of
lists of length @tt{n} in @secref["sec:background"]).

@(apply inline-code (extract braun.v "Braun"))

This says that the empty binary tree is a Braun tree of size
@tt{0}, and that if two numbers @tt{s_size}, @tt{t_size}
are the sizes of two Braun trees @tt{s} @tt{t}, and if
@tt{s_size <= t_size <= s_size + 1}, then combining
the @tt{s} and @tt{t} into a single tree produces
a braun tree of size @tt{s_size+t_size+1}.

Here is the insertion function:
@(apply inline-code (extract insert_no_gen.v "insert"))

It is fairly complex, so let us look carefully at each piece.
It accepts an object @tt{i} (of type @tt{A}) to insert into
the Braun tree @tt{b}. Its result type uses a new notation:
@inline-code|{
  {! «result variable» |:| «simple result type»
    |<| «running time variable» |>|
    «property of the function» !}
  }|
where the braces, exclamation marks, colons, less than, and
greater than are all fixed parts of the syntax and the 
portions enclosed in « » are filled in based on the
particulars of the insert function. In this case, it is
saying that
@tt{insert} returns a binary tree and, if the input is a
Braun tree of size @tt{n}, then the result is a Braun tree
of size
@tt{n+1} and the function takes @tt{fl_log n + 1} steps
of computation (where @tt{fl_log} computes the floor of the
base 2 logarithm).

These new @tt|{{! ... !}}| types are the types of
computations in the monad. The monad tracks the running
time as well as tracking the correctness property of the
function. Since we use a monadic type as the result of the 
function, we are saying that the function operates inside
the monad and thus we can track its running time and its
correctness properties.

The body of the @tt{insert} function begins with the
@tt{match} expression that determines if the input Braun
tree is empty or not. If it is empty, then the function
returns a singleton tree that is obtained by calling
@tt{bt_node} with two empty children. This case uses
@tt{<==}, the return operation that injects simple values
into the monad and @tt{+=} that declares that this simple
operation takes a single unit of computation. That is, the
type of @tt{+=} insists that it accepts a natural number 
@tt{k} and a computation in the monad taking some number of
steps, say @tt{n}. The result of @tt{+=} is also a
computation in the monad just like the second argument,
except that the running time is @tt{n+k}.

In the non-empty case, the insertion function recurs with
the right subtree and then builds a new tree with the sub-trees
swapped in order to preserve the Braun invariant. That is,
since we know that the left subtree's size is either equal to or one
larger than the right's, when we add an element to the right and swap
the subtrees, we will also end up with a new tree whose left
subtree's size is either equal to or one greater than the right.

The @tt{«var» <- «expr» ; «expr»} notation is the monadic bind
operator; if behaves much like a @tt{let} expression. The first,
right-hand side expression must be a computation in the monad;
the result value is pulled out of the monad and bound to 
@tt{var} for use in the body expression.
Then, as before, we return the new tree in the monad after treating
this as a single abstract step of computation.

Once this function is submitted to Coq, it responds with requests to
prove two claims, one from each of the cases of the function. The first
one is:
@inline-code{
forall n,
  Braun bt_mt n ->
   Braun (bt_node i bt_mt bt_mt) (n + 1) /\
   1 = fl_log n + 1
}
which may look a bit baroque. The left-hand side of the implication
is saying that we get to assume that @tt{n} is the size of
the empty binary tree. Of course, that tells us than @tt{n} must be
zero. So simplifying we are asked to prove that:
@inline-code{
Braun (bt_node i bt_mt bt_mt) 1
/\
1 = fl_log 0 + 1
}
both of which follow immediately from the definitions. Note that this
proof request corresponds exactly to what we need to know in order
for the base case to be correct: the singleton tree is a Braun tree
of size @tt{1} and the running time is correct when the input is empty.

For the second case, we are asked to prove:
@inline-code{
forall i j s t bt an n, 
  (forall m : nat, Braun t m -> 
     Braun bt (m + 1) /\ an = fl_log m + 1)
  Braun (bt_node j s t) n
  ->
  Braun (bt_node i bt s) (n + 1) /\ 
  an + 1 = fl_log n + 1
}
This is saying that we get to assume a slightly more general
inductive hypothesis (the inner @tt{forall}) than we need
(it is specialized to the recursive
call that @tt{insert} makes but not the size of the tree)
and that the tree @tt{bt_node j s t}
is a braun tree of size n. Given that, we must show that 
@tt{bt_node i bt s} is a Braun tree of size @tt{n + 1} and that
the running time is right.

Because the size information is not present in the actual
insertion function, Coq does not know to specialize the
inductive hypothesis to the size of @tt{t}. To clarify that
we can replace @tt{m} with @tt{t_size} and specialize
the first assumption to arrive at this theorem to prove
@inline-code{
 forall i j s t bt n t_size, 
  Braun bt (t_size + 1)
  an = fl_log t_size + 1
  Braun (bt_node j s t) (s_size + t_size + 1)
  ->
  Braun (bt_node i bt s) 
        (s_size + t_size + 1 + 1) /\ 
  an + 1 =
  fl_log (s_size + t_size + 1) + 1
}
which we can prove by using facts about logarithms
and the details of the definition of Braun trees.

Note also that this theorem corresponds precisely to what we 
need to know in order to prove that the recursive case
of @tt{insert} works. That is, the assumptions correspond to
the facts we gain from the input to the function and from
the result of the recursive call and the final result corresponds
to the facts we need to establish for this case.
