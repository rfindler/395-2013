#lang racket/base

(require scriblib/autobib)
(provide (all-defined-out))
(define-cite ~cite citet generate-bibliography)

;; need to check on this cite; just got it from Chris's paper
(define Braun
  (make-bib 
   #:title "A Logarithmic Implementation of Flexible Arrays"
   #:author (authors "W Braun" "M Rem")
   #:location (techrpt-location 
               #:number "MR83/4"
               #:institution "Eindhoven University of Technology")
   #:date 1983))
