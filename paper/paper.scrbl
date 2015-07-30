#lang scribble/lncs

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties
          racket/date)

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  A Coq Library For Internal Verification of Running-Times
}

@;@doi{@hspace[4] @bold{Draft as of @(date->string (seconds->date (current-seconds)))}}

@authors[@author[#:inst "1"]{Jay McCarthy}
         @author[#:inst "2"]{Burke Fetscher}
         @author[#:inst "2"]{Max New}
         @author[#:inst "2"]{Robert Bruce Findler}]

@institutes[
            @institute["University of Massachusetts at Lowell"
                       @linebreak[]
                       @email["jay.mccarthy@gmail.com"]]
            @institute["Northwestern University"
                       @linebreak[]
                       @email["{burke.fetscher, max.new, robby}@eecs.northwestern.edu"]]
]

@abstract{

 This paper presents a Coq library that lifts an abstract yet precise
notion of running-time into the type of a function.

 Our library is based on a monad that counts abstract steps,
controlled by one of the monadic operations. The monad's computational
content, however, is simply that of the identity monad so programs
written in our monad (that recur on the natural structure of their
arguments) extract into idiomatic OCaml code.

 We evaluated the expressiveness of the library by proving that
red-black tree insertion and search, merge sort, insertion sort,
Fibonacci, iterated list insertion, and Okasaki's Braun Tree
algorithms all have their expected running times.

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
