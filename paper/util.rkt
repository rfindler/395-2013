#lang racket/base
(require racket/runtime-path
         racket/string
         racket/match
         scribble/base
         scribble/core
         scribble/manual
         "extract.rkt")
(require (for-syntax racket/base))

(module+ test
  (require rackunit))

(define-runtime-path binds.v "binds.v")
(define-runtime-path braun.v "../common/braun.v")
(define-runtime-path insert.rkt "../insert/insert_log_gen.rkt")
(define-runtime-path monad.v "../monad/monad.v")
(define-runtime-path insert_log.v "../insert/insert_log.v")
(define-runtime-path insert_log_gen.v "../insert/insert_log_gen.v")
(define-runtime-path insert_no_gen.v "../insert/insert_nogen.v")
(define-runtime-path sub1_gen.v "../arith/sub1_gen.v")
(define-runtime-path sub1.v "../arith/sub1_gen.v")
(define-runtime-path sub1_linear_loop_gen.v "../arith/sub1_linear_loop_gen.v")
(define-runtime-path fib_iter_loop_gen.v "../fib/fib_iter_loop_gen.v")
(define-runtime-path copy_log_sq_gen.v "../copy/copy_log_sq_gen.v")
(define-runtime-path copy_log_sq.v "../copy/copy_log_sq.v")
(define-runtime-path extract.ml "../extract/extract.ml")
(define-runtime-path size_linear_gen.v "../size/size_linear_gen.v")
(define-runtime-path size_log_sq_gen.v "../size/size_log_sq_gen.v")
(define-runtime-path copy_linear_gen.v "../copy/copy_linear_gen.v")
(define-runtime-path diff_gen.v "../size/diff_gen.v")
(define-runtime-path size_linear_bin_gen.v "../size/size_linear_bin_gen.v")

(define-syntax (include-appendix stx)
  (syntax-case stx ()
    [_ (getenv "BUILD-WITH-APPENDIX") #'(include-section "appendix.scrbl")]
    [_ #'(void)]))
    

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

(define (chop-after reg lines)
  (cond
   [(null? lines)
    lines]
   [(regexp-match reg (car lines))
    null]
   [else
    (cons (car lines) (chop-after reg (cdr lines)))]))

(define (keep-after reg lines)
  (cond
   [(null? lines)
    lines]
   [(regexp-match reg (car lines))
    lines]
   [else
    (keep-after reg (cdr lines))]))

(module+ test
  (check-equal?
   (chop-after #rx"bad"
               (list "good" "good" "bad" "bad" "bad"))
   (list "good" "good")))

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
   #"\\newenvironment{InlineCode}{\\begin{trivlist}\\item\\footnotesize}{\\end{trivlist}}\n"))
