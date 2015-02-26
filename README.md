395-2013
========

This repo contains a monad for tracking running times for functions
written in Coq and a number of algorithms implemented using the monad.
(It's name comes from a PL seminar at Northwestern where this project
got its start.)

## To build:

Install coq verison 8.4 (September 2012) and Racket 6.1.1 (or later).

cd rkt/tmonad
raco pkg install

If you've got everything on your path, just run `make`. This will
check all of the proofs, extract OCaml code, and build the paper.

In general, each function whose running time is proven is first
written in a file name ending in `_gen.rkt`. The content of those
files is code in a specialized langauge that is a close mapping to Coq
with our monad, but with no typechecking and without the +=
expressions. Functions in that language, when compiled, automatically
insert the += expressions to compute running times and, when called,
return their results together with the running times. (This mode of
use is only intended for experimentation to try to learn facts about
the functions by graphing and the like). 

When you run one of the `_gen.rkt` files via the `racket`
command-line, it also prints out the Coq code with the += expressions
inserted. These printouts are then collected in to the `_gen.v` files
which are `Load`ed into the coq scripts.

## insert/ 

This directory contains the Braun tree insertion function.

## copy/, make_array/, size/

These directories contain the Coq implementation for functions from
[Chris Okasaki](http://www.usma.edu/eecs/SitePages/Chris%20Okasaki.aspx)'s
paper:

_Three algorithms on Braun trees_

Journal of Functional Programming

Volume 7 Issue 6, November 1997, 661 - 666

[pdf from citeseer](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.52.6090&rep=rep1&type=pdf)

## clrs/

This directory contains the implementation of the red-black tree
insert and lookup functions.

## sort/

This directory contains the implementation of insertion sort and merge sort.

## fib/ 

This directory contains the implementation of the naive recursive
implementation of fib and the linear time implementation.

## sub1/

This directory contains the implementation of sub1 (in terms of
constant time arithmetic operations)

## fold/

This directory contains the implementation of `fold`.

## monad/

This directory contains the implementation of the monad.

## paper/ 

This directory contains a writeup of the monad.

## extract/ 

This directory is where the extracted code is put by the Makefile.

## rkt/

  This directory contains the code that inserts the += expressions.

###  tmonad: 
  This file is the implementation of the transformation
  that inserts `+=` expressions. It is used as a language. That is, a
  program that begins 

    #lang at-exp s-exp tmonad

  contains a fully-parenthesized version of Coq. Running the main
  module of a program written in that language prints the Coq-syntax
  version of the file with the appropriate `+=` annotations in it.
  (Passing the file on the command-line runs the main module.) The
  file also turns into a Racket library that has an implementation of
  the definitions in the file. Those functions return all return two
  values: the actual result of the function and the abstract running
  time count. So, for example this module:

    #lang racket
    (require "insert_log_gen.rkt" tmonad)
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

### tmonad/coq

 This file contains a parser for a simple subset of Coq and produces
 programs in the language above. To use it, write:

    #reader tmonad/coq

 and it will parse the Coq-style notation and turn it into the
 language described above (for "tmonad").
