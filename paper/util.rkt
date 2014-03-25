#lang racket/base
(require racket/runtime-path
         racket/string
         racket/match
         scribble/base
         scribble/core
         scribble/manual
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
(define-runtime-path extract.ml "../extract/extract.ml")

(define (keep-range reg lines)

  (define (drop-up-to reg lines)
    (let loop ([lines lines])
      (cond
        [(null? lines) lines]
        [else
         (cond
           [(regexp-match reg (car lines))
            lines]
           [else (loop (cdr lines))])])))  
  
  (reverse
   (drop-up-to 
    reg
    (reverse (drop-up-to reg lines)))))

(provide extract
         (all-defined-out))

(define (raw-latex . args)
  (element (style "relax" '(exact-chars))
           args))

(define (snoc l x)
  (append l (list x)))

(define (trim-blank-from-end l)
  (match-define (list before ... last (regexp #px"^[:space:]*$" (list _)) ...) l)
  (snoc before (string-trim last #:left? #f)))

(define (inline-code . args)
  (compound-paragraph
   (style "InlineCode" '())
   (list 
    (apply
     verbatim
     (trim-blank-from-end args)))))

(define extra-tex-code
  (bytes-append
   #"\\usepackage{pslatex}\n"
   #"\\usepackage{inconsolata}\n"
   #"\\newenvironment{InlineCode}{\\begin{trivlist}\\item}{\\end{trivlist}}\n"))
