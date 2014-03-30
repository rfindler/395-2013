#lang racket/base
(require racket/match
         racket/contract)

(provide (struct-out Fp)
         (struct-out coq-arg)
         out-Fp
         out-prefix)

(define (out-prefix name)
  (out "(* this file was generated automatically ")
  (when name
    (out "from ") 
    (out name)
    (out " "))
  (out "*)")
  (out-nl))

(struct Fp (name args measure result body))
(struct coq-arg (name string))
(define (out-Fp an-Fp)
  (match an-Fp
    [(Fp id args measure result body)
     (out "Program Fixpoint ")
     (out id)
     (for ([arg (in-list args)])
       (out " ")
       (out (coq-arg-string arg)))
     (when measure
       (out " {measure ")
       (out measure)
       (out "}"))
     (out-nl)
     (out ": {! res !:! ")
     (out result)
     (out " !<! c !>!")
     (out-nl)
     (out "     ")
     (out id)
     (out "_result")
     (for ([i (in-list args)])
       (out " ")
       (out (coq-arg-name i)))
     (out " res c !} :=")
     (indent
      2
      (out-nl)
      (out-exp body #:already-delimited? #t)
      (out "."))
     (out-nl)]))

(define (out-exp exp #:already-delimited? [already-delimited? #f])
  (define wrap-with-parens? (and (not already-delimited?)
                                 (not (simple? exp))))
  (when wrap-with-parens? (out "("))
  (indent
   (if wrap-with-parens? 1 0)
   (match exp
     [`(match (,texp1 ,texp2 ...) [,tsts1 ,tsts2 ... => ,rexps] ...)
      (out "match ")
      (out-exp texp1)
      (for ([texp (in-list texp2)])
        (out ", ")
        (out-exp texp))
      (out " with")
      (indent 
       2
       (for ([fst-tst (in-list tsts1)]
             [rst-tsts (in-list tsts2)]
             [rexp (in-list rexps)])
         (out-nl)
         (out "| ")
         (out-pat fst-tst)
         (for ([rst-tst (in-list rst-tsts)])
           (out ", ")
           (out-pat rst-tst))
         (out " => ")
         (indent 2 
                 (out-nl)
                 (out-exp rexp #:already-delimited? #t))))
      (out-nl)
      (out "end")]
     [`(bind ([,xs ,es] ...) ,b)
      (for ([x (in-list xs)]
            [e (in-list es)])
        (out-id x)
        (out " <- ")
        (indent (+ 4 (string-length (symbol->string x)))
                (out-exp e #:already-delimited? #t))
        (out ";")
        (out-nl))
      (out-exp b #:already-delimited? #t)]
     [`(if ,e1 ,e2 ,e3)
      (out "if ")
      (indent 3 (out-exp e1))
      (out-nl)
      (out "then ")
      (indent 5 (out-exp e2))
      (out-nl)
      (out "else ")
      (indent 5 (out-exp e3))]
     [(? symbol?) (out-id exp)]
     [(? number?) (out-const exp)]
     [`(<== ,e)
      (out "<== ")
      (indent 4 (out-exp e))]
     [`(+= ,k ,e)
      (out "+= ")
      (out k)
      (out "; ")
      (out-nl)
      (out-exp e #:already-delimited? #t)]
     [`(,(? infixop? fn) ,arg1 ,args ...)
      (out-exp arg1)
      (for ([arg (in-list args)])
        (out " ")
        (out fn)
        (out " ")
        (out-exp arg))]
     [`(,(? symbol? fn) ,args ...)
      (out fn)
      (for ([arg (in-list args)])
        (out " ")
        (out-exp arg))]))
  (when wrap-with-parens? (out ")")))

(define (infixop? x) (member x '(- + *)))
(define (compound-expression? exp) (pair? exp))
(define (simple? exp) (or (symbol? exp) (number? exp)))
(define (out-id id)
  (out (string->symbol (regexp-replace* #rx"′" (symbol->string id) "'"))))
(define (out-const n) (out n))

(define-syntax-rule (indent n exp ...)
  (letrec ([_indentation indentation])
    (set! indentation (+ indentation n))
    exp ...
    (set! indentation _indentation)))

(define indentation 0)
(define (out-nl) 
  (out "\n")
  (for ([_ (in-range indentation)])
    (out " ")))
(define (out s) (display s))

(define (out-pat exp)
  (define flat-pat? (or/c symbol? number?))
  (match exp
    [`(,(? flat-pat?) ...) 
     (for ([x (in-list exp)]
           [i (in-naturals)])
       (unless (zero? i) (out " "))
       (out-flat-pat x))]
    [(? flat-pat?)
     (out-flat-pat exp)]))

(define (out-flat-pat exp)
  (if (symbol? exp)
      (out-id exp)
      (out exp)))
