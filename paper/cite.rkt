#lang racket/base

(require scriblib/autobib)
(provide (except-out (all-defined-out) fpca jfp types icfem waaapl))
(define-cite ~cite citet generate-bibliography)

(define fpca
  "Proc. International Conference on Functional Programming Languages And Computer Architecture")
(define jfp
  "Journal of Functional Programming")
(define types
  "Proc. Workshop of the Working Group Types")
(define icfem
  "Proc. International Conference on Formal Engineering Methods and Software Engineering")
(define waaapl
  "Proc. Workshop on Algorithmic Aspects of Advanced Programming Languages")
(define esop
  "Proc. European Symposium on Programming")
(define tphols
  "Proc. Theorem Proving in Higher Order Logics")
(define popl
  "Proc. Symposium on Principles of Programming Languages")

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
