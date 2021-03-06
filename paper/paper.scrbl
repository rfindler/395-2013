#lang scribble/elsarticle

@(require "util.rkt" "cite.rkt" 
          scriblib/footnote
          scribble/core
          scribble/latex-properties
          racket/date)

@title[#:style (style #f (list (tex-addition extra-tex-code)))]{
  A Coq Library For Internal Verification of Running-Times
}

@;@doi{@hspace[4] @bold{Draft as of @(date->string (seconds->date (current-seconds)))}}

@frontmatter[
             #:authors
             (list @author{Jay McCarthy}
                   @email["jay.mccarthy@gmail.com"]
                   @address["University of Massachusetts at Lowell"]
                   @author{Burke Fetscher}
                   @email["burke.fetscher@eecs.northwestern.edu"]
                   @author{Max S. New}
                   @email["max.new@eecs.northwestern.edu"]
                   @author{Daniel Feltey}
                   @email["daniel.feltey@eecs.northwestern.edu"]
                   @author{Robert Bruce Findler}
                   @email["robby@eecs.northwestern.edu"]
                   @address["Northwestern University"])
             #:abstract
             @abstract{

                       This paper presents a Coq library that lifts an
abstract yet precise notion of running-time into the type of a
function. Our library is based on a monad that counts abstract steps.
The monad's computational
content, however, is simply that of the identity monad so programs
written in our monad (that recur on the natural structure of their
arguments) extract into idiomatic OCaml code.

  We evaluated the
expressiveness of the library by proving that red-black tree insertion
and search, merge sort, insertion sort, various Fibonacci number implementations,
iterated list insertion, various BigNum operations, and Okasaki's Braun Tree algorithms all
have their expected running times.
}]

@section{Introduction}

For some programs, proving that they have correct input-output
behavior is only part of the story. As @citet[complexity-dos]
observed, incorrect performance characteristics can lead
to security vulnerabilities. Indeed, some programs and algorithms
are valuable precisely because of their performance
characteristics. For example, merge sort is preferable to insertion
sort only because of its improved running time.
Unfortunately, defining functions in Coq or other theorem
proving systems does not provide enough information in the types to
state these intensional properties.

Our work provides a monad (implemented as a library in Coq) that
enables us to include abstract running times in types. We use this
library to prove that several important algorithms have their expected
running times.

The monad in our work has similar goals to the one in
@citet[lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures]'s,
but with two benefits.
First, it allows programmers
to write idiomatic code without embedding invariants in data types,
so we can reason about a wider variety of programs. Second, and more
significantly, our monad adds no complexity
computations to the extracted OCaml code, so the verification
imposes no run-time overhead.  We elaborate these details and differences
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
different functions. @Secref["sec:prims"] and @secref["sec:other-prims"]
discuss accounting for the running time of various language
primitives. Finally, @secref["sec:related-work"] provides a detailed
account of our relation to similar projects. Our source code and other
supplementary material is available at
@url{https://github.com/rfindler/395-2013}.

@bold{Extended material:} Compared to the conference proceedings
version of this paper@~cite[coq-library-conference-version], this version contains more elaborate and
detailed figures and proofs throughout, as well as an extended
discussion of language primitive runtimes in @secref["sec:prims"].

@include-section["insert.scrbl"]

@include-section["running-time.scrbl"]

@include-section["extract-insert.scrbl"]

@include-section["monad.scrbl"]

@include-section["case-study.scrbl"]

@include-section["prims.scrbl"]

@include-section["other-prims.scrbl"]

@include-section["related-work.scrbl"]
	
@;@section{Conclusion}

@generate-bibliography[]

@(include-appendix)
