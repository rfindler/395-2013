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
- size (extraction)
- copy_linear (time, correctness, extraction)
- copy_fib (time, correctness, extraction)
- copy_log2 (time, correctness, extraction)
- make_array_naive (time, correctness, extraction) [max]
- make_array_td (time, correctness, extraction)
- make_array_bu (time, correctness, extraction)
- to_list (time, correctness, extraction)
