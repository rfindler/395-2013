#lang racket/base

(require parser-tools/lex
         parser-tools/yacc
         syntax/readerr
         racket/list
         (prefix-in : parser-tools/lex-sre))

(provide read-syntax read)

(define (read port)
  (parse (object-name port) port))
(define (read-syntax name port)
  (parameterize ([current-mod-name (if (path? name)
                                       (let-values ([(base name dir?) (split-path name)])
                                         (string->symbol
                                          (regexp-replace #rx"[.][^.]*$" (path->string name) "")))
                                       'anonymous-module)])
    (datum->syntax #f (parse name port))))

(define (parse src port)
  (port-count-lines! port)
  (define (next-token) 
    (parameterize ([current-source src])
      (simple-coq-lexer port)))
  (ws-lexer port)
  (simple-coq-parser next-token))
  
(define-empty-tokens coq-empty-tokens
  (Program 
   Fixpoint
   colon
   :=
   period
   
   Provide
   
   brace-! !:! !<! !>! !-brace 
   
   <- semicolon += <== 
   
   match comma with pipe => end
   
   open-brace close-brace open-paren close-paren
   
   eof))
(define-tokens coq-tokens
  (id))

(define-lex-abbrev ws (:* whitespace))

(define (ws-lexer port)
  (regexp-match #rx"[ \t\n]*" port))

(define simple-coq-lexer
  (lexer-src-pos
   [(:: "Provide" ws) (token-Provide)]
   [(:: "Program" ws) (token-Program)]
   [(:: "Fixpoint" ws) (token-Fixpoint)]
   [(:: "{" ws) (token-open-brace)]
   [(:: "}" ws) (token-close-brace)]
   [(:: "(" ws) (token-open-paren)]
   [(:: ")" ws) (token-close-paren)]
   [(:: ":=" ws) (token-:=)]
   [(:: ":" ws) (token-colon)]
   [(:: "." ws) (token-period)]
   [(:: "{!" ws) (token-brace-!)]
   [(:: "!:!" ws) (token-!:!)]
   [(:: "!<!" ws) (token-!<!)]
   [(:: "!>!" ws) (token-!>!)]
   [(:: "!}" ws) (token-!-brace)]
   [(:: "<-" ws) (token-<-)]
   [(:: ";" ws) (token-semicolon)]
   [(:: "," ws) (token-comma)]
   [(:: "+=" ws) (token-+=)]
   [(:: "<=="  ws) (token-<==)]
   [(:: "match" ws) (token-match)]
   [(:: "|" ws) (token-pipe)]
   [(:: "with" ws) (token-with)]
   [(:: "=>" ws) (token-=>)]
   [(:: "end" ws) (token-end)]
   [(:: (:+ "@" (:/ "a" "z" "A" "Z"))
        (:* (:+ "_" (:/ "a" "z" "A" "Z" "0" "9"))) 
        ws)
    (token-id (string->symbol (regexp-replace #rx"[\t\n ]*$" lexeme "")))]
   ["(*" (begin (read-nested-comment 1 start-pos input-port)
                (ws-lexer input-port)
                (return-without-pos (simple-coq-lexer input-port)))]
   [(eof) (token-eof)]))

(define get-next-comment
  (lexer
   ["(*" (values 1 end-pos)]
   ["*)" (values -1 end-pos)]
   [(:or "*" ")" (:* (:~ "*" ")")))
    (get-next-comment input-port)]
   [(eof) (values 'eof end-pos)]
   [(special)
    (get-next-comment input-port)]
   [(special-comment)
    (get-next-comment input-port)]))

(define (read-nested-comment num-opens start-pos input)
  (let-values (((diff end) (get-next-comment input)))
    (cond
      ((eq? 'eof diff) (raise-read-error "eof in commments .... <need srcloc info>"))
      (else
       (let ((next-num-opens (+ diff num-opens)))
         (cond
           ((= 0 next-num-opens) "")
           (else (read-nested-comment next-num-opens start-pos input))))))))

(define simple-coq-parser
  (parser 
   (grammar
    [start ((defns) `(module ,(current-mod-name) "tmonad.rkt" ,@$1))]
    [defns
      ((defn) (list $1))
      ((defn defns) (cons $1 $2))]
    [defn
      ((Program Fixpoint id args colon type := expr period)
       `(Fixpoint ,$3 ,@$4 #:returns (,$6) ,$8))
      ((Provide id period)
       `(provide ,$2))]
    [args ((arg) $1)
          ((arg args) (append $1 $2))]
    [arg ((open-brace id colon type close-brace) 
          `(#:implicit (,$2 ,$4)))
         ((open-paren id colon type close-paren)
          `((,$2 ,$4)))]
    [type ((ids) (apply string-append (add-between (map symbol->string $1) " ")))]
    [ids ((id) (list $1))
         ((id ids) (cons $1 $2))]
    [expr-comma-list
     ((expr) (list $1))
     ((expr comma expr-comma-list)
      (cons $1 $3))]
    [expr ((match expr-comma-list with match-cases end)
           `(match ,$2 ,@$4))
          ((open-paren expr close-paren) $2)
          ((id <- expr semicolon expr) 
           `(bind ((,$1 ,$3)) ,$5))
          ((id) $1)
          
          ;; application needs at least two ids (could be exprs --ack!)
          ((id ids) (cons $1 $2))
          
          ((<== expr) `(<== ,$2))]
    [match-cases ((pipe pat => expr)
                  (list `[,$2 => ,$4]))
                 ((pipe pat => expr match-cases)
                  (cons `[,$2 => ,$4] $5))]
    [pat ((id) $1)
         ((open-paren pat close-paren) $2)
         ((ids) $1)])
   
   (tokens coq-empty-tokens coq-tokens)
   (error 
    (λ (tok-ok? tok-name tok-value start-pos end-pos)
      (raise-read-error
       (format "could not parse, starting from ~a at loc ~a" 
               tok-name
               (position-offset start-pos))
       (current-source)
       (position-line start-pos)
       (position-col start-pos)
       (position-offset start-pos)
       (- (position-offset end-pos)
          (position-offset start-pos)))))
   (end eof)
   (start start)
   (src-pos)))

(define current-mod-name (make-parameter 'anonymous-module))
(define current-source (make-parameter #f))
