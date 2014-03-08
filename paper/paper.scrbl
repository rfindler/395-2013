#lang scribble/sigplan

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties)

@title[#:style (style #f (list (tex-addition #"\\usepackage{inconsolata}\n")))]{
  Putting Dependent Types to Work
  @subtitle{A Coq Library That Enforces Correct Running-Times via Type-Checking}}
@doi{}

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

@abstract{
 This paper presents a Coq library that lifts
 a notion of running-time into the type of a
 function and uses it to prove all nine of the algorithms
 in Okasaki's paper @italic{Three Algorithms on Braun 
  Trees} are correct and have the claimed running times.
  
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

@section{Introduction}

Running times! Whoo hoo!

@include-section["background.scrbl"]

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@include-section["extract-insert.scrbl"]

@include-section["monad.scrbl"]

@section[#:tag "sec:case-study"]{Case Study}

in the Braun tree functions @tt{copy_linear}, @tt{copy_fib},
@tt{copy2}, and @tt{make_array_td} because they split a natural or a
list in half for each recursive call. (final version of bind)


We did all of Chris's paper. See git repo.

Found a few other things:

Fold.

The bonus argument to bind (already in monad section?)

the extraction is "polluted" by functions that are defined by more complex recursive schemes.

Other things?

@include-section["prims.scrbl"]

@section{Related Work}

@citet[a-machine-checked-proof-of-the-average-case-complexity-of-quicksort-in-coq]

@citet[automatic-complexity-analysis]

@citet[characteristic-formulae-for-mechanized-program-verification]

@citet[correct-by-construction-model-transformations]

@citet[dependently-typed-datastructures]

@citet[functors-for-proofs-and-programs]

@citet[hoare-logic-state-monad]

@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]

@citet[three-algorithms-on-braun-trees]

@section{Conclusion}

@generate-bibliography[]