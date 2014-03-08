#lang racket/base

(require scriblib/autobib)
(provide (all-defined-out))
(define-cite ~cite citet generate-bibliography)

(define fpca
  "Proc. International Conference on Functional Programming Languages And Computer Architecture")

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