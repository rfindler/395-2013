#lang scribble/base

@(require "util.rkt" scriblib/footnote)

@title[#:tag "sec:extract-insert"]{Extracting the @tt{insert} Function}

One of the important benefits of our library is that
none of the correctness conditions and running time
infrastructure affects Coq's extraction process.
In particular, our monad extracts as the identity
monad, which means that the OCaml code produced by Coq
does not require any modifications.

For example, here is how @tt{insert} extracts:
@inline-code{
type 'a bin_tree =
| Bt_mt
| Bt_node of 'a * 'a bin_tree * 'a bin_tree

 let rec insert i = function
| Bt_mt -> 
  Bt_node (i, Bt_mt, Bt_mt)
| Bt_node (j, s, t) -> 
  Bt_node (i, (insert j t), s)
}
This code does not have any proof residue, unlike the code
extracted for @tt{drop} in @secref["sec:extraction-tmi"].