#lang scribble/base
@(require "util.rkt" 
          "line-counts.rkt"
          "cite.rkt"
          scriblib/figure)

@(define fun-count "17")

@title[#:tag "sec:case-study"]{Case Study}

@; XXX This table isn't formatted correctly for LNCS.
@figure*["fig:line-counts" "Line Counts"]{@build-table[]}

To better understand how applicable our monad is, we implemented the
search and insertion functions for red-black trees, insertion sort,
merge sort, both the naive recursive version of the nth Fibonacci
number function and the linear time version, a function that inserts
@raw-latex{$m$} times into a list at position @raw-latex{$n$} using
both lists and zippers, and all of the algorithms mentioned in
@citet[three-algorithms-on-braun-trees]'s paper, @italic{Three
Algorithms on Braun Trees}.  Okasaki's paper contains several versions
of each of the three functions, each with different running times, in
each case culminating with efficient versions.
The three functions are:
@itemlist[@item{@tt{size}: computes the size of a Braun tree 
                 (a linear and a log squared version)}
          @item{@tt{copy}: builds a Braun tree a given size
                 filled entirely with a given element
                 (a linear, a fib ∘ log, a log squared, and a log time version),
                 and}
          @item{@tt{make_array}: convert a list into a Braun tree
                 (two n log n versions and a linear version).}]  In
total, we implemented @fun-count different functions using the monad.
For all of them, we proved the expected Big O running times.  For
merge sort, we proved it is Big O(@raw-latex{$n \log(n)$}) and Big
Ω(@raw-latex{$n \log(n)$}). For the naive fib, we proved that it is
Big Ω and Big O of itself, Big O(2@raw-latex{$^n$}), and Big
Ω(2@raw-latex{$^{n/2}$}). For the list insertion functions, we prove
that when @raw-latex{$m$} is positive, the zipper version is Big O of
the list version (because the zipper version runs in Big
O(@raw-latex{$m + n$}) while the list version runs in Big
O(@raw-latex{$n * m$}). We also prove correctness, except for
@tt{make_array_linear} and red-black tree insertion where we proved
only the running times.

The supplementary material contains all of the Coq code for all of the
functions in our case study.

@section{Line Counts}

The line counts for the various implementations of the algorithms
using our monad are shown in @figure-ref["fig:line-counts"].  The
files whose names end in @tt{gen.v} are the output of the script that
inserts @tt{+=} expressions, so they contain the definitions of the
various functions, but without the correctness conditions (or any of
the proofs or data structure definitions). There are more than @fun-count
because a number of the functions needed helper functions that are in
the monad (and thus require running time proofs).  As you can see, the
functions are generally short. The proofs are typically much longer.

We divided the line counts up into proofs that are inside obligations
(and thus correspond to establishing that the monadic types are
correct) and other lines of proofs. With the exception of the
@tt{make_array_linear} and the red-black tree insertion function, 
the proofs inside the obligations establish the correctness of the
functions and establish a basic running time result, 
but not one in terms of Big O. 

@figure["fig:copy_log_sq"
        @list{@tt{copy_log_sq}}
        @(apply inline-code (extract copy_log_sq_gen.v cdr))
        @raw-latex{\vspace{-3em}}]

For example, @Figure-ref["fig:copy_log_sq"] is the definition of the
@tt{copy_log_sq} function, basically mirroring Okasaki's definition,
but in Coq's notation. The monadic result type is
@(apply inline-code (extract copy_log_sq.v "copy_insert_result"))
which says that the result is a Braun tree whose size matches the
input natural number, that linearizing the resulting tree
produces the input list, and that the running time is given by
the function @tt{copy_log_sq_time}.

The running time function, however, is defined in parallel to
@tt{log_sq} itself, not as the product of the logs: @(apply
inline-code (extract copy_log_sq.v "copy_insert_time")) This parallel
definition makes it straightforward to prove that @tt{copy_log_sq}'s
running time equals @tt{copy_log_sq_time}, but leaves as a separate
issue the proof that @tt{copy_log_sq_time} is Big O of the square of
the log. There are 56 lines of proof to guarantee the result type of
the function is correct and an additional 179 lines to prove that that
@tt{copy_log_sq_time} is Big O of the square of the log.

For the simpler functions (every one with linear running time except
@tt{make_array_linear}), the running time can be expressed directly in
the monadic result (with precise constants). However, for most of the
functions the running time is first expressed precisely in a manner
that matches the structure of the function and then that running time
is proven to correspond to some asymptotic complexity, as with
@tt{copy_log_sq}. The precise line counts can be read off of the
columns in @figure-ref["fig:line-counts"].

The @tt{Monad} and @tt{Common} lines count the number of lines of code
in our monad's implementation (including the proofs of the monad laws)
and some libraries used in multiple algorithms, including a Big O
library, a Log library, and some common facts and definitions about
Braun trees.

@section{Extraction}

The extracted functions naturally fall into three categories.

In the first category are functions that recur on the natural
structure of their inputs, e.g., functions that process lists from the
front--one element at a time, functions that process trees by
processing the children and combining the result, and so on. In the
second category are functions that recursively process numbers by
counting down by ones from a given number.  In the third category are
functions that ``skip'' over some of their inputs. For example, in
Okasaki's algorithms, functions recur on natural numbers by dividing the
number by 2 instead of subtracting one, and merge sort recurs by
dividing the list in half at each step.

Functions in the first category extract into precisely the OCaml code
that you would expect, just like @tt{insert}, as discussed in
@secref["sec:insert"].

Functions in the second category could extract like the first, except
because we extract Coq's @tt{nat} type, which is based on Peano
numerals, into OCaml's @tt{big_int} type, which has a different
structure, a natural @tt{match} expression in Coq becomes a more
complex pattern in OCaml. A representative example of this pattern is
@tt{zip_rightn}. Here is the extracted version:

@(apply inline-code
        (extract 
         extract.ml 
         (λ (all-lines)
           (trim-blank-from-end
            (chop-after #rx"zip_leftn"
                        (keep-after #rx"let rec zip_rightn" all-lines))))))

The body of this function is equivalent to a single conditional that
returns @tt{z} when @tt{n} is @tt{0} and recursively calls
@tt{zip_rightn} on @tt{n-1} otherwise. This artifact in the extraction
is simply a by-product of the mismatch between @tt{nat} and
@tt{big_int}. We expect that this artifact can be automatically
removed by the OCaml compiler. This transformation into the single
conditional corresponds to modest inlining, since @tt{fO} and @tt{fS}
occur exactly once and are constants.

Functions in the third category, however, are more complex. They
extract into code that is cluttered by Coq's support for non-simple
recursion schemes. Because each function in Coq must be proven to be
well-defined and to terminate on all inputs, functions that don't
simply follow the natural recursive structure of their input must have
supplemental arguments that record the decreasing nature of their
input. After extraction, these additional arguments clutter the OCaml
code with useless data structures equivalent to the original set of
arguments.

The function @tt{cinterleave} is one such function. Here is the
extracted version:

@(apply inline-code
        (extract 
         extract.ml 
         (λ (all-lines)
           (trim-blank-from-end
            (chop-after #rx"val cinterleave"
                        (keep-after #rx"let rec cinterleave_func" all-lines))))))

@(apply inline-code
        (extract 
         extract.ml 
         (λ (all-lines)
           (trim-blank-from-end
            (chop-after #rx"to_list_naive"
                        (keep-after #rx"let cinterleave e" all-lines))))))

All of the extra pieces beyond what was written in the original
function are useless. In particular, the argument to
@tt{cinterleave_func} is a three-deep nested pair containing @tt{__}
and two lists. The @tt{__} is a constant that is defined at the top of
the extraction file that is never used for anything and behaves like
@tt{unit}. That piece of the tuple corresponds to a proof that the
combined length of the two lists is decreasing. The function starts by
destructuring this complex argument to extract the two lists, @tt{e}
and @tt{o}. Next it constructs a version of the function,
@tt{cinterleave0}, that recovers the natural two argument function for
use recursively in the body of the @tt{match} expression. Finally,
this same two argument interface is reconstructed a second time,
@tt{cinterleave}, for external applications. The external interface
has an additional layer of strangeness in the form of applications of
@tt{Obj.magic} which can be used to coerce types, but here is simply
the identity function on values and in the types. These calls
correspond to use of @tt{proj1_sig} in Coq to extract the value from a
Sigma type and are useless and always successful in OCaml.

All together, the OCaml program is equivalent to:

@inline-code{
let rec cinterleave e o =
    match e with | Nil -> o
                 | Cons (x, xs) -> Cons (x, (cinterleave o xs))
}

This is exactly the Coq program and idiomatic OCaml code.  Unlike the
second category, it is less plausible that the OCaml compiler already
performs this optimization and removes the superfluity from the Coq
extraction output. However, it is plausible that such an optimization
pass could be implemented, since it corresponds to inlining,
de-tupling, and removing an unused @tt{unit}-like argument. In
summary, the presence of these useless terms is unrelated to our
running time monad, but is an example of the sort of verification residue
we wish to avoid and do successfully avoid in the case of the running
time obligations.

The functions in the first category are: @tt{insert},
@tt{size_linear}, @tt{size}, @tt{make_array_naive}, @tt{foldr},
@tt{make_array_naive_foldr}, @tt{unravel}, @tt{to_list_naive},
@tt{isort}'s @tt{insert}, @tt{isort}, @tt{clength}, @tt{minsert_at},
@tt{to_zip}, @tt{from_zip}, @tt{zip_right}, @tt{zip_left},
@tt{zip_insert}, @tt{zip_minsert}, @tt{minsertz_at}, @tt{bst_search},
@tt{rbt_blacken}, @tt{rbt_balance}, @tt{rbt_insert}.

The functions in the second category are: @tt{fib_rec}, @tt{fib_iter},
@tt{sub1}, @tt{mergesort}'s @tt{split}, @tt{insert_at},
@tt{zip_rightn}, @tt{zip_leftn}.

The functions in the third category are: @tt{copy_linear},
@tt{copy_fib}, @tt{copy_log_sq}, @tt{copy2}, @tt{diff},
@tt{make_array_td}, @tt{cinterleave}, @tt{merge}, @tt{mergesort}. Some
of the functions in the second category are also in the third
category.

