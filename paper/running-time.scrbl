#lang scribble/base
@(require scriblib/figure
          "util.rkt"
          "cite.rkt"
          racket/list
          scribble/core)

@;{ This is a version of verbatim to support the figure below; the only change is
    that it returns a list of the lines, not the actual table}
@(define (hacked-verbatim #:indent [i 0] s . more)
  (define lines 
    ;; Break input into a list of lists, where each inner
    ;; list is a single line. Break lines on "\n" in the
    ;; input strings, while non-string content is treated
    ;; as an element within a line.
    (let loop ([l (cons s more)] [strs null])
      (cond
       [(null? l) (if (null? strs)
                      null
                      (map
                       list
                       (regexp-split
                        #rx"\n"
                        (apply string-append (reverse strs)))))]
       [(string? (car l))
        (loop (cdr l) (cons (car l) strs))]
       [else
        (define post-lines (loop (cdr l) null))
        (define pre-lines (loop null strs))
        (define-values (post-line rest-lines)
          (if (null? post-lines)
              (values null null)
              (values (car post-lines) (cdr post-lines))))
        (define-values (first-lines pre-line)
          (if (null? pre-lines)
              (values null null)
              (values (drop-right pre-lines 1)
                      (last pre-lines))))
        (append first-lines
                (list (append pre-line (list (car l)) post-line))
                rest-lines)])))
  (define (str->elts str)
    ;; Convert a single string in a line to typewriter font,
    ;; and also convert multiple adjacent spaces to `hspace` so
    ;; that the space is preserved exactly:
    (let ([spaces (regexp-match-positions #rx"(?:^| ) +" str)])
      (if spaces
        (list* (make-element 'tt (substring str 0 (caar spaces)))
               (hspace (- (cdar spaces) (caar spaces)))
               (str->elts (substring str (cdar spaces))))
        (list (make-element 'tt (list str))))))
  (define (strs->elts line)
    ;; Convert strings in the line:
    (apply append (map (lambda (e) 
                         (if (string? e) 
                             (str->elts e) 
                             (list e)))
                       line)))
  (define indent
    ;; Add indentation to a line:
    (if (zero? i)
      values
      (let ([hs (hspace i)]) (lambda (line) (cons hs line)))))
  (define (make-nonempty l)
    ;; If a line has no content, then add a single space:
    (if (let loop ([l l])
          (cond
           [(null? l) #t]
           [(equal? "" l) #t]
           [(list? l) (andmap loop l)]
           [(element? l) (loop (element-content l))]
           [(multiarg-element? l) (loop (multiarg-element-contents l))]
           [else #f]))
        (list l (hspace 1))
        l))
  (define (make-line line)
    ;; Convert a list of line elements --- a mixture of strings
    ;; and non-strings --- to a paragraph for the line:
    (let* ([line (indent (strs->elts line))])
      (list (make-paragraph omitable-style (make-nonempty line)))))
  (map make-line lines))
@(define omitable-style (make-style 'omitable null))

@title[#:tag "sec:running-time"]{Implicit Running Times}

@figure*["fig:translation" "Inserting += into insert"]{
@(let ()
   (define (drop-leading-comment l)
     (unless (regexp-match #rx"^ *[(][*][^*]*[*][)] *$" (car l))
       (error 'drop-leading-comment 
              "first line appears to not be a comment ~s" 
              (car l)))
     ;; right now we know generation inserts
     ;; a single line that has the comment 'automatically generated'
     ;; use 'cdr' to drop it.
     (cdr l))
   (define (map-append/blanks l1 l2)
     (define len (max (length l1) (length l2)))
     (define (add-on l) 
       (append l 
               (hacked-verbatim
                (build-string
                 (- len (length l))
                 (λ (_) #\newline)))))
     (map append
          (add-on l1)
          (add-on l2)))
   (make-table
    plain
    (map-append/blanks
     (apply hacked-verbatim (extract insert.rkt "insert"))
     (apply hacked-verbatim (extract insert_log_gen.v drop-leading-comment)))))
@raw-latex{\vspace{-5em}}
}

One disadvantage to the code in the previous section is that the
running times are tangled with the body of the insertion function.
Even worse, making mistakes when writing @tt{+=} expressions can
produce un-provable claims or cause our proofs about the running times
to be incorrect and useless, as they will prove facts that are
irrelevant to the functions we are using.

To handle this situation, we have written a simple Coq-to-Coq
translation function that accepts functions written in our monad
without any @tt{+=} expressions and turns them into ones with @tt{+=}
expressions in just the right places.

Our translation function accepts a function written in the
monad, but without the monadic type on its result, and produces
one with it. For example, the @tt{insert} function shown on the
left in @figure-ref["fig:translation"] is translated into the one
on the right. As well as adding @tt{+=} expressions, the
translation process also generates a call to @tt{insert_result}
in the monadic result type. The user must define this function 
separately and the translation's output must be used in that
context:
@(apply inline-code (extract insert_log.v "insert_result"))

Unlike the previous version, this one accounts for the larger constant
factors and it also includes a stricter correctness condition to show
that we establish complete functional correctness. Specifically, the
new conjunct uses @tt{SequenceR} (a proposition from our library) to
insist that if you linearize the resulting Braun tree into a list,
then it is the same as linearizing the input and consing the new
element onto the front of the list.

Rather than develop a novel, and potentially controversial cost
semantics, we show the utility of our monad by adopting the
@citet[automatic-complexity-analysis] cost model. This model treats
each function call, variable lookup, and case-dispatch as a single
unit of abstract time. In @figure-ref["fig:translation"], the first
return is annotated with a cost of @raw-latex{$6$} because it
references @raw-latex{$4$} variables, calls @raw-latex{$1$} function,
and does @raw-latex{$1$} case-dispatch. The second return is annotated
with a cost of @raw-latex{$9$} because it references @raw-latex{$6$}
variables (the self-reference is not counted), calls @raw-latex{$2$}
functions, and does @raw-latex{$1$} case-dispatch.

Our translation function is straightforward and is included in the
supplementary materials (@tt{add-plusses/check-stx-errs} in
@tt{rkt/tmonad/main.rkt}). Our monad could support different cost
semantics, without modification, provided a function could map them to
the program's syntax in a straightforward way and provided they met
certain constraints. Specifically, we assume that costs are
compositionally additive. This means that a live heap consumption
cost, such as @citet[albert-heap] or @citet[montenegro-space] could
not be used. However, a semantics like
@citet[machine-checked-union-find]'s that only counts unit cost at
function entry would be straightforward. We implement a simplified semantics
like this. It is particularly interesting because the default,
specific semantics treats all arithmetic operations as having unit
cost, which may not be the most reliable measure as we discuss in
@secref["sec:prims"].

An alternative approach would be to follow
@citet[static-cost-analysis] and build a Coq model of a machine and
programming language. We would then define a cost judgement for this
machine and prove its soundness with respect to the machine's
reduction lengths. Finally, we would show that our monadic types allow
incremental proofs of their cost results. In some sense, this ``deep
embedding'' would be a more direct study of cost and cost proofs, but
it would be no more directly connected with the running time of the
programs, unless we could establish a connection to the OCaml VM and
the hardware itself.
