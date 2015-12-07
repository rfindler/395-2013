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
         @author[#:inst "2"]{Daniel Feltey}
         @author[#:inst "2"]{Robert Bruce Findler}]

@institutes[
            @institute["University of Massachusetts at Lowell"
                       @linebreak[]
                       @email["jay.mccarthy@gmail.com"]]
            @institute["Northwestern University"
                       @linebreak[]
                       @email["{burke.fetscher, max.new, daniel.feltey, robby}@eecs.northwestern.edu"]]
]

@abstract{

This paper presents a Coq library that lifts an abstract yet precise
notion of running-time into the type of a function. Our library is
based on a monad that counts abstract steps, controlled by one of the
monadic operations. The monad's computational content, however, is
simply that of the identity monad so programs written in our
monad (that recur on the natural structure of their arguments) extract
into idiomatic OCaml code. We evaluated the expressiveness of the
library by proving that red-black tree insertion and search, merge
sort, insertion sort, Fibonacci, iterated list insertion, BigNum
addition, and Okasaki's Braun Tree algorithms all have their expected
running times.

}

@section{Introduction}

For some programs, proving that they have correct input-output
behavior is only part of the story. As @citet[complexity-dos]
observed, incorrect performance characteristics can also lead
to security vulnerabilities. Indeed, some programs and algorithms
are valuable precisely because of their performance
characteristics. For example, mergesort is preferable to insertion
sort only because of its improved running time.
Unfortunately, defining functions in Coq or other theorem
proving systems does not provide enough information in the types to be
able to state these intensional properties.

Our work provides a monad (implemented as a library in Coq) that
enables us to include abstract running times in types. We use this
library to prove several important algorithms have their expected
running times.  Unlike
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]'s
approach, our library has two benefits. First, it allows programmers
to write idiomatic code without embedding invariants in the data type,
so we can reason about a wider variety of programs. Second, and more
significantly, we guarantee that our monad adds no complexity
computations to the extracted OCaml code, so it has no verification
overhead on running time.  We elaborate these details and differences
throughout the paper and, in particular, in
@secref["sec:related-work"].

The rest of the paper is structured as follows. In
@secref["sec:insert"], we give an overview of how the library works
and the style of proofs we support. In @secref["sec:running-time"], we
discuss the cost model our proofs deal with. In
@secref["sec:extract-insert"], we explain the extraction of our
programs to OCaml. In these first three sections, we use a consistent
example that is introduced in @secref["sec:insert"]. Following this
preamble, @secref["sec:monad"] walks through the definition and design
of the monad itself. @Secref["sec:case-study"] describes the results
of our case study, wherein we proved properties of a variety of
different functions. @Secref["sec:sub1"] discusses accounting for
the runtimes of various language primitives. Finally,
@secref["sec:related-work"] provides a detailed account of our relation
to similar projects. Our source code and other supplementary material
is available at @url{http://github.com/rfindler/395-2013}.

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@include-section["extract-insert.scrbl"]

@include-section["monad.scrbl"]

@include-section["case-study.scrbl"]

@include-section["prims.scrbl"]

@include-section["related-work.scrbl"]
	
@;@section{Conclusion}

@generate-bibliography[]
