#lang racket/base

(require scriblib/autobib)
(provide (except-out (all-defined-out) fpca jfp types icfem waaapl))
(define-cite ~cite citet generate-bibliography)

(define fpca
  "Proc. Intl. Conference on Functional Programming Languages And Computer Architecture")
(define jfp
  "Journal of Functional Programming")
(define icfp
  "Proc. Intl. Conference on Functional Programming")
(define types
  "Proc. Workshop of the Working Group Types")
(define icfem
  "Proc. Intl. Conference on Formal Engineering Methods and Software Engineering")
(define itp
  "Proc. Intl. Conference on Interactive Theorem Proving")
(define waaapl
  "Proc. Workshop on Algorithmic Aspects of Advanced Programming Languages")
(define esop
  "Proc. European Symposium on Programming")
(define tphols
  "Proc. Theorem Proving in Higher Order Logics")
(define popl
  "Proc. Symposium on Principles of Programming Languages")
(define pldi
  "Proc. Conference on Programming Language Design and Implementation")
(define plpv
  "Proc. Workshop on Programming Languages meets Program Verification")
(define fossacs
  "Proc. Foundations of Software Science and Computation Structure")
(define usenix-sec
  "Proc. USENIX Security Symposium")

;; need to check on this cite; just got it from Chris's paper
(define Braun
  (make-bib 
   #:title "A Logarithmic Implementation of Flexible Arrays"
   #:author (authors "W Braun" "M Rem")
   #:location (techrpt-location 
               #:number "MR83/4"
               #:institution "Eindhoven University of Technology")
   #:date 1983))

(define automatic-complexity-analysis
  (make-bib
   #:title "Automatic Complexity Analysis"
   #:author "Mads Rosendahl"
   #:location (proceedings-location fpca)
   #:date 1989))

(define three-algorithms-on-braun-trees
  (make-bib
   #:title "Three Algorithms on Braun Trees"
   #:author "Chris Okasaki"
   #:location (journal-location jfp #:number 6 #:volume 7)
   #:date 1997))

(define a-machine-checked-proof-of-the-average-case-complexity-of-quicksort-in-coq
  (make-bib
   #:title "A Machine-Checked Proof of the Average-Case Complexity of Quicksort in Coq"
   #:author (authors "Eelis van der Weegen" "James McKinna")
   #:location (proceedings-location types)
   #:date 2008))

(define characteristic-formulae-for-mechanized-program-verification
  (make-bib
   #:title "Characteristic Formulae for Mechanized Program Verification"
   #:author "Arthur Charguéraud"
   #:location (dissertation-location
               #:institution "Université Paris Diderot (Paris 7)"
               #:degree "PhD")
   #:date 2010))

(define machine-checked-union-find
  (make-bib
   #:title "Machine-checked verification of the correctness and amortized complexity of an efficient union-find implementation"
   #:author (authors "Arthur Charguéraud" "François Pottier")
   #:location (proceedings-location itp)
   #:date 2015))

(define correct-by-construction-model-transformations
  (make-bib
   #:title (string-append "Correct-by-Construction Model Transformations"
                          " from Partially Ordered Specifications in Coq")
   #:author (authors "Iman Poernomo" "Jeffrey Terrell")
   #:location (proceedings-location icfem)
   #:date 2010))

(define dependently-typed-datastructures
  (make-bib
   #:title "Dependently Typed Data Structures"
   #:author "Hongwei Xi"
   #:location (proceedings-location waaapl)
   #:date 1999))

(define dependent-types-in-practical-programming-diss
  (make-bib
   #:title "Dependently Types in Practical Programming"
   #:author "Hongwei Xi"
   #:location (dissertation-location #:institution "Carnegie Mellon University")
   #:date 1999))

(define dependent-types-in-practical-programming-popl
  (make-bib
   #:title "Dependently Types in Practical Programming"
   #:author (authors "Hongwei Xi" "Frank Pfenning")
   #:location (proceedings-location popl)
   #:date 1999))

(define functors-for-proofs-and-programs
  (make-bib
   #:title "Functors for Proofs and Programs"
   #:author (authors "Jean-Christophe Filliâtre"
                     "Pierre Letouzey")
   #:location (proceedings-location esop)
   #:date 2004))

(define hoare-logic-state-monad
  (make-bib
   #:title "A Hoare Logic for the State Monad"
   #:author "Wouter Swierstra"
   #:location (proceedings-location tphols)
   #:date 2009))
   
(define lightweight-semiformal-time-complexity-analysis-for-purely-functional-data-structures
  (make-bib
   #:title "Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures"
   #:author "Nils Anders Danielsson"
   #:location (proceedings-location popl)
   #:date 2008))


(define Program-cite
  (make-bib
   #:title "Subset Coercions in Coq"
   #:author "Matthieu Sozeau"
   #:location (proceedings-location types)
   #:date 2006))

(define Atkey-generalized-monad
  (make-bib
   #:title "Parameterised Notions of Computation"
   #:author "Robert Atkey"
   #:location (journal-location jfp #:number "3-4" #:volume 19)
   #:date 2009))
  
(define ACU-generalized-monad
  (make-bib
   #:title "Monads Need Not Be Endofunctors"
   #:author (authors "Thorsten Altenkirch" "James Chapman" "Tarmo Uustalu")
   #:location (proceedings-location fossacs)
   #:date 2010))

(define speed
  (make-bib 
   #:title "SPEED: Precise and Efficient Static Estimation of Program Computational Complexity"
   #:author (authors "Sumit Gulwani" "Krishna K. Mehra" "Trishul Chilimbi")
   #:location (proceedings-location popl)
   #:date 2009))

(define static-cost-analysis
  (make-bib 
   #:title "A Static Cost Analysis for a Higher-order Language"
   #:author (authors "Norman Danner" "Jennifer Paykin" "James S. Royer")
   #:location (proceedings-location plpv)
   #:date 2013))

(define auto-parallel
  (make-bib
   #:title "Automatic Static Cost Analysis for Parallel Programs"
   #:author (authors "Jan Hoffmann" "Zhong Shao")
   #:location (proceedings-location esop)
   #:date 2015))

(define auto-heap
  (make-bib
   #:author (authors "Martin Hofmann" "Steffen Jost")
   #:title "Static prediction of heap space usage for first-order functional programs"
   #:location (proceedings-location popl)
   #:date 2003))

(define recursion-in-bounded-space
  (make-bib
   #:author (authors "John Hughes" "Lars Pareto")
   #:title "Recursion and Dynamic Data-structures in bounded space: Towards Embedded ML Programming"
   #:location (proceedings-location icfp)
   #:date 1999))

(define resource-bound-certification
  (make-bib
   #:author (authors "Karl Crary" "Stephanie Weirich")
   #:title "Resource bound certification"
   #:location (proceedings-location popl)
   #:date 2000))

(define dijkstra-monad
  (make-bib
   #:author (authors "Nikhil Swamy" "Joel Weinberger" "Cole Schlesinger"
                     "Juan Chen" "Benjamin Livshits")
   #:title "Verifying Higher-order Programs with the Dijkstra Monad"
   #:location (proceedings-location pldi)
   #:date 2013))

(define clrs
  (make-bib
   #:author (authors "Thomas H. Cormen" "Charles E. Leiserson"
                     "Ronald L. Rivest" "Clifford Stein")
   #:title "Introduction to Algorithms (3rd Edition)"
   #:location "MIT Press"
   #:date 2009))

(define complexity-dos
  (make-bib
   #:author (authors "Scott A. Crosby" "Dan S. Wallach")
   #:title "Denial of Service via Algorithmic Complexity Attacks"
   #:location (proceedings-location usenix-sec)
   #:date 2003))
