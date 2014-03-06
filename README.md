395-2013
========

This repo contains Coq code for functions from
[Chris Okasaki](http://www.usma.edu/eecs/SitePages/Chris%20Okasaki.aspx)'s
paper:

_Three algorithms on Braun trees_

Journal of Functional Programming

Volume 7 Issue 6, November 1997, 661 - 666

[pdf from citeseer](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.52.6090&rep=rep1&type=pdf)

To build:

  Use coq verison 8.4 (September 2012) and Racket 6.0 (or later).

  Run 'make' twice. The first time should finish everything except the
  extraction, but will end with an error. Run make a second time and
  it should pick up where it left off, completing the extraction.


TODO:
- size_diff (redo with Racket generation, big_oh)   [robby]
- make_array_bu (time, correctness, extraction, big_oh) [max]
- to_list_naive (exact time [vs bound], big_oh)
- to_list_bu (time, correctness, extraction, big_oh)
- investigate sub1's running time (should we consider it constant?)
- improve coq parser and use it everywhere [robby]
- move the rest of the files out of tmonad/ into function-specific directories [robby]
- rename the files in rkt/ to match the new naming convention (the
  function name followed by the running time) [robby]

