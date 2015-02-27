#lang scribble/sigplan @10pt

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties
          racket/date)

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  A Coq Library For Internal Verification of Running-Times
}
@doi{@hspace[4] @bold{Draft as of @(date->string (seconds->date (current-seconds)))}}

@authorinfo["Jay McCarthy"
            "Vassar College"
            "jay.mccarthy@gmail.com"]
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
 function.

 Our library is based on a monad that counts abstract steps,
 controlled by one of the monadic operations. The monad's
 computational content, however, is simply that of the identity
 monad so programs written in our monad (that recur on the natural
 structure of their arguments) extract into idiomatic OCaml code.
 
 We evaluated the library by proving that red-black trees,
 merge sort, insertion sort, fib, and Okasaki's
 Braun Tree algorithms all have their expected running times.
}

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@include-section["extract-insert.scrbl"]

@include-section["monad.scrbl"]

@include-section["case-study.scrbl"]

@include-section["prims.scrbl"]

@include-section["related-work.scrbl"]
	
@;@section{Conclusion}

@generate-bibliography[]
