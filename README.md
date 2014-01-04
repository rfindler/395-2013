395-2013
========

This repo contains Coq code for functions from
[Chris Okasaki](http://www.usma.edu/eecs/SitePages/Chris%20Okasaki.aspx)'s
paper:

_Three algorithms on Braun trees_

Journal of Functional Programming

Volume 7 Issue 6, November 1997, 661 - 666

[pdf from citeseer](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.52.6090&rep=rep1&type=pdf)

original
=======

First approach

omonad
======

First monadic approach, had poor extraction

logical
=======

Based on logical relations and proofs of decidability

TODO:
- Two variants of copy (correctness + timing)
- Bottom-up make_array (correctness + timing)
- Sequence finding (inverse of make_array) algorithm (correctness + timing)

tmonad
======

New monadic approach, with improved extraction

TODO:
- try to share code related to correctness [jay]
- insert (correctness) [jay]
- extraction setup [jay]
- size_linear (time, correctness) [Max]
- size (time, correctness) [robby]
- copy_linear (time, correctness)
- copy_fib (time, correctness)
- copy_log2 (time, correctness)
- make_array_naive (time, correctness)
- make_array_td (time, correctness)
- make_array_bu (time, correctness)
- to_list (time, correctness)
