#lang racket/base
(require racket/runtime-path
         scribble/base
         scribble/core
         "extract.rkt")

(define-runtime-path lwl.v "lwl.v")
(define-runtime-path l.v "l.v")
(define-runtime-path binds.v "binds.v")
(define-runtime-path braun.v "../common/braun.v")
(define-runtime-path insert.rkt "../rkt/insert.rkt")
(define-runtime-path monad.v "../tmonad/monad.v")
(define-runtime-path insert_log.v "../insert/insert_log.v")
(define-runtime-path insert_log_gen.v "../insert/insert_log_gen.v")
(define-runtime-path insert_no_gen.v "../insert/insert_nogen.v")
(define-runtime-path sub1_gen.v "../sub1/sub1_gen.v")
(define-runtime-path copy_log_sq_gen.v "../copy/copy_log_sq_gen.v")
(define-runtime-path copy_log_sq.v "../copy/copy_log_sq.v")

(provide extract
         (all-defined-out))

(define (inline-code . args)
  (compound-paragraph
   (style "InlineCode" '())
   (list (apply verbatim args))))

(define extra-tex-code
  (bytes-append
   #"\\usepackage{inconsolata}\n"
   #"\\newenvironment{InlineCode}{\\begin{trivlist}\\item}{\\end{trivlist}}\n"))
