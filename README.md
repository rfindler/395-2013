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
- size_diff (redo with Racket generation, big_oh)   [robby]
- make_array_td (redo with Racket generation, big_oh)
- make_array_bu (time, correctness, extraction, big_oh) [max]
- to_list_naive (exact time [vs bound], big_oh)
- to_list_bu (time, correctness, extraction, big_oh)
- investigate sub1's running time (should we consider it constant?)
- improve coq parser and use it everywhere [robby]
- rearrange the files & directories in the repo [robby]
