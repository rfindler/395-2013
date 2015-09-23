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

@section{Introduction}

For some programs, proving that they have correct input-output
behavior is only part of the story. As @citet[complexity-dos]
observed, incorrect performance characteristics can also lead
to security vulnerabilities. Indeed, some programs and algorithms
are valuable precisely because of their performance
characteristics (for instance, compare mergesort and insertion
sort). Unfortunately, defining functions in Coq or other theorem
proving systems does not provide enough information in the types to be
able to state these intentional properties.

Our work provides a monad (implemented as a library in Coq) that
enables us to include abstract running times in types. We use this
library to prove several important algorithms have their expected
running times.
Unlike @citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]'s
approach, our library has two benefits. First, it allows programmers to write
idiomatic code without embedding invariants in
the data type, so we can reason about a wider variety of
programs. Second, and more significantly, we guarantee that no
complexity computations are embedded in the extracted code, so the
extracted program reads like idiomatic OCaml code and has no
verification overhead at runtime. We elaborate these details and
differences throughout the paper and, in particular, in
@secref["related-work"].

The rest of the paper XXX.

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@include-section["extract-insert.scrbl"]

@include-section["monad.scrbl"]

@include-section["case-study.scrbl"]

@;@include-section["prims.scrbl"]

@include-section["related-work.scrbl"]
	
@;@section{Conclusion}

@generate-bibliography[]
