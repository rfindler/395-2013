395-2013
========

This repo contains Coq code for functions from
[Chris Okasaki](http://www.usma.edu/eecs/SitePages/Chris%20Okasaki.aspx)'s
paper:

_Three algorithms on Braun trees_

Journal of Functional Programming

Volume 7 Issue 6, November 1997, 661 - 666

[pdf from citeseer](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.52.6090&rep=rep1&type=pdf)

## To build:

  Install coq verison 8.4 (September 2012) and Racket 6.0 (or later).
  And if you've got everything on your path, just run 'make'. This will
  check all of the proofs, extract ocaml code, and build the paper.

## rkt/

  This directory contains the code that inserts the += expressions and
  all of the implementations of the functions from Okasaki's paper.

###  tmonad.rkt: 
  This file is the implementation of the transformation
  that inserts `+=` expressions. It is used as a language. That is, a
  program that begins 

    #lang at-exp s-exp "tmonad.rkt"

  contains a fully-parenthesized version of Coq. Running the main
  module of a program written in that language prints the Coq-syntax
  version of the file with the appropriate `+=` annotations in it.
  (Passing the file on the command-line runs the main module.) The
  file also turns into a Racket library that has an implementation of
  the definitions in the file. Those functions return all return two
  values: the actual result of the function and the abstract running
  time count. So, for example this module:

    #lang racket
    (require "insert.rkt" "tmonad.rkt")
    (insert 3 (bt_node 1 (bt_node 2 bt_mt bt_mt) bt_mt))

  prints out:

    (bt_node 3 (bt_node 1 #0=bt_mt #0#) (bt_node 2 #0# #0#))
    15

  showing the result of doing the insertion (the `#0#` notation shows
  the sharing in the result; in this case it is showing the
  uninteresting result that there is only a single empty tree, so they
  are all shared) and the abstract running time.

  This is the grammar for the precise language that is allowed:

    A top-level definition is one of:
      (provide <id>)
      (require <relative-path>)
      (Fixpoint <id> <fp-arg> ... #:returns <type> <exp>)

    An fp-arg is one of:
      @<id>{<type>}
      #:implicit @<id>{<type>}

    An exp is one of:
      (match (<exp> ...) (<pat> <pat> ... => <exp) ...)
      (if <exp> <exp> <exp>)
      (bind ([<id> <exp>]) <exp>) -- bind in the monad
      (<mnid> <exp> ...)   -- call to a function that doesn't return something in the monad
      (<id> <exp> ...)     -- call to a function that returns        something in the monad
      (<== <exp>)
      <id>
      <constant>

    A pat is either:
      <id>
      (<id> <id> ...)

 An id follows the usual syntax, with one exception: if it begins with
 an underscore, the it is included in the Coq-generated output, but
 dropped from the Racket version. This feature is intended to support
 `foldr`; the Racket-level version of `foldr` doesn't have the loop
 invariant argument, but the Coq version needs it.

 One gotcha to watch out for: the @-notation is based on 
 [Scribble](http://docs.racket-lang.org/scribble/) and thus it requires
 special escapes when there is an @ in the type. So, when a function
 accepts an argument `bt` of type `@bin_tree A`, then we have to write 
 `@bt{@"@"bin_tree A}`.

### tmonad-coq.rkt

 This file contains a parser for a simple subset of Coq and produces
 programs in the language above. To use it, write:

    #reader "tmonad-coq.rkt"

 and it will parse the Coq-style notation and turn it into the
 language described above (for "tmonad.rkt").


TODO: 
 - make_array_bu (time, correctness, extraction, big_oh) [robby]
 - to_list_naive (exact time [vs bound], big_oh) 
 - to_list_bu (time, correctness, extraction, big_oh) 


