#lang scribble/base
@(require "util.rkt" 
          "line-counts.rkt"
          scriblib/figure)

@title[#:tag "sec:case-study"]{Case Study}

@figure*["fig:line-counts" "Line Counts"]{@build-table[]}

in the Braun tree functions @tt{copy_linear}, @tt{copy_fib},
@tt{copy2}, and @tt{make_array_td} because they split a natural or a
list in half for each recursive call. (final version of bind)


We did all of Chris's paper. See git repo.

Found a few other things:

Fold.

The bonus argument to bind (already in monad section?)

the extraction is "polluted" by functions that are defined by more complex recursive schemes.

Other things?
