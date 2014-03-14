#lang scribble/sigplan

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties)

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
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
