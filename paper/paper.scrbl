#lang scribble/sigplan @10pt

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties
          racket/date)

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  Putting Dependent Types to Work
  @subtitle{A Coq Library That Enforces Correct Running-Times via Type-Checking}}
@doi{@hspace[4] @bold{Draft as of @(date->string (seconds->date (current-seconds)))}}

@authorinfo["Jay McCarthy"
            "Brigham Young University"
            "jay@cs.byu.edu"]
@authorinfo["Burke Fetscher"
            "Northwestern University"
            "burke.fetscher@eecs.northwestern.edu"]
@authorinfo["Max New"
            "Northwestern University"
            "max.new@eecs.northwestern.edu"]
@authorinfo["Robert Bruce Findler"
            "Northwestern University"
            "robby@eecs.northwestern.edu"]

@;{ Aaron's comments:

Hi, guys.

I read through your Putting Dependent Types to Work paper (actually more than once) a while back, but did not find a moment to write to you about it until just now, with baby napping...

I really like that you are tackling running time in type theory.  I think this is a major issue that has been largely ignored by the type theory community.  The monadic approach is a natural one, and since the type theory does not help you out (since it considers Ackermann(4,2) interchangeable -- syntactically indistinguishable -- from 2^65536 − 3), one has to resort to providing an interface where the semantics you are trying to enforce cannot actually be expressed inside the theory.  So this all seems really reasonable.  I also quite like the Braun tree example.  I did not know about this data structure, but can think of at least one interesting use for it.  And it is, of course, very nice that you can formally verify the results from Osaki about this data structure.

One piece of terminology I like with dependent types, which your paper made me think of, is internal versus external verification.  An internally verified artifact is one which, thanks to rich typing (or you could just say, imposition of invariants directly in the artifact), carries with it its own verification in some sense.  An externally verified artifact is one which has some property proved about it by a distinct proof artifact.  We can have internally and externally verified data structures: lists with length are internally verified, and lists where we impose some additional property outside the list itself (like, length l = 10, or sorted l, or something like that) are externally verified.  Functions can be internally verified, if they have pre- and post-conditions expressed in their types; or externally verified, if you write some theorem about them.  It is hard to see how to verify certain kinds of properties internally; algebraic properties like commutativity of addition or associativity of list append seem hard to express with the types of those functions.  When doing internal verification of a function, one could capture a precondition on a data structure internally or externally: either the function takes in x with a rich type, or x with a simple type together with a proof p about x.

So in your case, I would say your monad is supporting internal verification of functions, where you oropose using externally verified data structures (your functions take in binary trees together with proofs that they are Braun) for better extraction.

One quibble: I do not understand your choice of title, since lots of previous research has indeed been putting dependent types to work already, so this does not seem unique to your work.

That aside, I like the paper and wish you the best for acceptance at OOPSLA!

Cheers,
Aaron

------ from a followup message

For the terminology cite:

> I got the terminology from some lecture notes of Thorsten Altenkirch's:
>
> http://www.cs.nott.ac.uk/~txa/publ/esslli96.pdf

}

@abstract{
 This paper presents a Coq library that lifts
 an abstract yet precise notion of running-time into the type of a
 function and uses it to prove all nine of the algorithms
 in Okasaki's paper @italic{Three Algorithms on Braun 
  Trees} have the claimed running times.
  
 A secondary goal of this paper is to be an introduction to
 Coq. While Coq is never going to
 be as straight-forward as Logo or Scratch, it has
 has the capacity to write amazingly rich specifications
 of functions and, once you have done so, the corresponding
 proofs can be only as complex as they need to be in order
 to actually establish the specified properties. 
 This paper assumes only that its readers are familiar with
 ordinary, tree-processing functions and that they are
 willing to dig into very precise specifications of
 such functions. No familiarity with Coq itself is assumed.
}

@;@section{Introduction}

@include-section["background.scrbl"]

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@include-section["extract-insert.scrbl"]

@include-section["monad.scrbl"]

@include-section["case-study.scrbl"]

@include-section["prims.scrbl"]

@include-section["related-work.scrbl"]
	
@;@section{Conclusion}

@generate-bibliography[]
