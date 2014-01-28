#lang scribble/sigplan

@(require "util.rkt" scriblib/footnote)

@title{Putting Dependent Types to Work
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

@section{Introduction}

Running times! Whoo hoo!

@include-section{background.scrbl}

@section{Proving Braun-Tree Insertion is O(nlogn)}

Demo of @tt{insert} code here. Brief discussion of 
proofs (i.e., say they are "auto" with a few facts about logs)

@section{The Monad}

Can we stage this explanation? Do a simpler version of the monad first?

@section{Evaluation}

We did all of Chris's paper. See git repo.

Found a few other things:

Fold.

The bonus argument to bind.

Other things?

@section{Related Work}

@section{Conclusion}
