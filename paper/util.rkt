#lang racket/base
(require racket/runtime-path
         scribble/base
         "extract.rkt")

(define-runtime-path lwl.v "lwl.v")
(define-runtime-path l.v "l.v")
(define-runtime-path braun.v "../common/braun.v")
(define-runtime-path insert.rkt "../rkt/insert.rkt")
(define-runtime-path monad.v "../tmonad/monad.v")
(define-runtime-path insert_log.v "../insert/insert_log.v")
(define-runtime-path insert_log_gen.v "../insert/insert_log_gen.v")
(define-runtime-path insert_no_gen.v "../insert/insert_nogen.v")

(provide extract
         (all-defined-out))

(define (inline-code . args)
  (apply verbatim args))
