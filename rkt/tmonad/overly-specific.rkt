#lang racket/base
(require tmonad/private/the-lang)
(provide (except-out
          (all-from-out 
           tmonad/private/the-lang)
          Fixpoint))
(provide (rename-out [overly-specific-Fixpoint Fixpoint]))
