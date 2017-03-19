#lang racket/base

(require (for-syntax racket/match racket/base)
         racket/contract
         (prefix-in r: racket/match))

(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         define-syntax
         #%datum
         #%app
         Fixpoint overly-specific-Fixpoint
         bt_mt
         bt_node
         CT_leaf
         CT_node
         BLACK
         RED
         match if bind let => <==
         provide
         require for-syntax
         cons list
         nil
         pair fst snd
         left right
         even_odd_dec even_oddb
         le_lt_dec
         div2
         S
         (rename-out [-:nat -])
         + * pred
         double double_plus1
         false true
         andb orb xorb negb
         proj1_sig
         (rename-out [coq:_ _]))

(define coq:_ (let ()
                (struct coq:_ ())
                (coq:_)))

(define (proj1_sig x) x)

(define-syntax (top-interaction stx)
  (syntax-case stx ()
    [(_ . e) #'e]))

(define-syntax (module-begin stx)
  (syntax-case stx ()
    [(_ args ...)
     (with-syntax ([name (let ([src (syntax-source stx)])
                           (cond
                             [(path? src) 
                              (define-values (base name dir?) (split-path src))
                              (format "~a" name)]
                             [else #'#f]))])
       #`(#%module-begin
          (module+ main (require tmonad/emit) (out-prefix name))
          #,@(for/list ([arg (in-list (syntax->list #'(args ...)))])
               (syntax-case arg ()
                 [(id . whatever)
                  (ormap (λ (x) (and (identifier? x)
                                     (free-identifier=? x #'id)))
                         (list #'Fixpoint #'provide #'require))
                  arg]
                 [_ #`(top-interaction . #,arg)]))))]))

(define-for-syntax (nmid? x)
  (and (identifier? x)
       (member x (syntax->list #'(pair bt_node CT_node cons)) free-identifier=?)))

(define-for-syntax (parse-Fixpoint-arg stx arg implicit?)
  (syntax-case arg ()
    [id
     (identifier? arg)
     (values arg
             #`(coq-arg
                'id
                #,(if implicit?
                    (format "{~a}" (symbol->string (syntax-e arg)))
                    (symbol->string (syntax-e arg)))))]
    [(id strs ...)
     (and (identifier? #'id)
          (andmap (λ (x) (string? (syntax-e x)))
                  (syntax->list #'(strs ...))))
     (let ()
       (define brackets (if implicit? "{~a:~a}" "(~a:~a)"))
       (values
        #'id
        #`(coq-arg
           'id
           #,(format
              brackets
              (syntax-e #'id)
              (apply string-append (map syntax-e (syntax->list #'(strs ...))))))))]
    [_
     (raise-syntax-error #f "malformed arg" stx arg)]))

(define-for-syntax (parse-Fixpoint-args stx args)
  (let loop ([args args]
             [racket-args '()]
             [coq-args '()]
             [measure #f])
    (syntax-case args ()
      [(#:implicit arg . args)
       (let ()
         (define-values (racket-arg coq-arg) (parse-Fixpoint-arg stx #'arg #t))
         (loop #'args racket-args (cons coq-arg coq-args) measure))]
      [(#:measure the-measure . args)
       (begin
         (unless (or (identifier? #'the-measure)
                     (string? (syntax-e #'the-measure)))
           (raise-syntax-error #f "expected an identifier or a string for the measure argument"))
         (loop #'args racket-args coq-args #'the-measure))]
      [(#:returns result)
       (let ()
         (define res-strs (syntax->list #'result))
         (unless res-strs
           (raise-syntax-error #f "expected a sequence of strings" 
                               stx 
                               #'result))
         (for ([x (in-list res-strs)])
           (unless (string? (syntax-e x))
             (raise-syntax-error #f "expected a string" 
                                 stx 
                                 x)))
         (values (reverse racket-args)
                 (reverse coq-args)
                 (apply string-append (map syntax-e res-strs))
                 measure))]
      [(kw . args)
       (keyword? (syntax-e #'kw))
       (raise-syntax-error 
        #f 
        "unexpected keyword, expected one of #:implicit, #:measure, or #:returns"
        stx #'kw)]
      [(arg . args)
       (let ()
         (define-values (racket-arg coq-arg) (parse-Fixpoint-arg stx #'arg #f))
         (loop #'args (cons racket-arg racket-args) (cons coq-arg coq-args) measure))]
      [()
       (raise-syntax-error #f "didn't find #:returns keyword" stx)])))

(define-for-syntax (do-Fixpoint stx overly-specific?)
  (syntax-case stx ()
    [(_ id args ... body)
     (begin
       (unless (identifier? #'id)
         (raise-syntax-error 'Fixpoint "expected identifier"
                             stx #'id))
       (define-values (racket-args coq-args coq-result measure)
         (parse-Fixpoint-args stx #'(args ...)))
       (define exp (add-plusses/check-stx-errs #'body overly-specific?))
       #`(begin
           (module+ main
             (require tmonad/emit)
             (out-Fp (Fp 'id (list #,@coq-args) '#,measure #,coq-result '#,exp)))
           (define (id #,@racket-args)
             (begin #,(if (identifier? measure)
                          measure
                          #'(void))
                    #,exp))))]))

(define-syntax (Fixpoint stx) (do-Fixpoint stx #f))
(define-syntax (overly-specific-Fixpoint stx) (do-Fixpoint stx #t))

(define-for-syntax (add-plusses/check-stx-errs orig-stx overly-specific?)
  (define (in-monad k stx)
    (syntax-case stx (match if bind => <==)
      [(match (t ...) [ps1 ps2 ... => es] ...)
       ;; destructuring matches are free
       (let ([inc (if (= 1 (length (syntax->list #'(ps1 ...)))) 0 1)])
         (when (null? (syntax->list #'(t ...)))
           (raise-syntax-error 'match "expected at least one test" stx))
         (for ([ps (in-list (syntax->list #'((ps1 ps2 ...) ...)))])
           (for ([p (in-list (syntax->list ps))])
             (check-match-pattern p)))
         (define ts-cost 
           (for/sum ([t (in-list (syntax->list #'(t ...)))])
             (count-expr t)))
         (define addl-k (+ inc ts-cost))
         (with-syntax  ([(mes ...)
                         (for/list ([e (in-list (syntax->list #'(es ...)))])
                           (in-monad (+ k addl-k) e))])
           #`(match (t ...) [ps1 ps2 ... => mes] ...)))]
      [(match x . args)
       (identifier? #'x)
       (raise-syntax-error #f "expected a sequence of identifiers" orig-stx #'x)]
      [(match x . cases)
       (let ()
         (define lst (syntax->list #'cases))
         (when lst
           (for ([case (in-list lst)])
             (syntax-case case ()
               [(stuff ...)
                (unless (for/or ([stuff (in-list (syntax->list #'(stuff ...)))])
                          (and (identifier? stuff)
                               (free-identifier=? #'=> stuff)))
                  (raise-syntax-error #f "expected => in match" orig-stx case))]
               [_ (void)])))
         (raise-syntax-error #f "malformed match" orig-stx stx))]
      [(if tst thn els)
       (let ()
         (define addl-k (+ 1 (count-expr #'tst)))
         #`(if tst
             #,(in-monad (+ k addl-k) #'thn)
             #,(in-monad (+ k addl-k) #'els)))]
      [(if . args)
       (raise-syntax-error #f "malformed if" orig-stx stx)]
      [(bind ([x rhs]) body)
       (let ()
         (define-values (rhs-k rhs-t) (in-monad/!tail #'rhs))
         #`(bind ([x #,rhs-t])
                 #,(in-monad (+ 1 k rhs-k) #'body)))]
      [(bind . args)
       (raise-syntax-error #f "malformed bind" orig-stx stx)]
      [(f x ...)
       (nmid? #'f)
       (raise-syntax-error #f "non-monad returning function in a monad place"
                           orig-stx #'f)]
      [(<== e)
       (add+= (if overly-specific? 
                  (+ k (count-expr #'e))
                  1)
              stx)]
      [(f x ...)
       (identifier? #'f)
       (raise-syntax-error #f "calls to functions must be bound in binds"
                           orig-stx stx)]
      [_ (raise-syntax-error #f "expected an expression in the monad" stx)]))

  (define (in-monad/!tail stx)
    (syntax-case stx (match if bind => <==)
      [(match . whatever)
       (raise-syntax-error #f "match must not occur in non-tail position"
                           orig-stx stx)]
      [(if tst thn els)
       (raise-syntax-error #f "if must not occur in non-tail position"
                           orig-stx stx)]
      [(bind ([x rhs]) body)
       (raise-syntax-error #f "bind must not occur in non-tail position"
                           orig-stx stx)]
      [(f x ...)
       (nmid? #'f)
       (raise-syntax-error #f "non-monad returning function in a monad place"
                           orig-stx #'f)]
      [(<== e)
       (values (count-expr #'e) stx)]
      [(f x ...)
       (identifier? #'f)
       (let ()
         (define extra
           (for/sum ([e (in-list (syntax->list #'(x ...)))])
                    (count-expr e)))
         (values (+ extra) stx))]
      [_ (raise-syntax-error #f "expected an expression in the monad" stx)]))
  
  (define (count-expr stx)
    (syntax-case stx (match if bind => <==)
      [(match . whatever)
       (raise-syntax-error #f "cannot count a `match' outside of the monad"
                           orig-stx stx)]
      [(if . whatever)
       (raise-syntax-error #f "cannot count an `if' outside of the monad"
                           orig-stx stx)]
      [(bind . whatever)
       (raise-syntax-error #f "found `bind' outside of the monad"
                           orig-stx stx)]
      [(<== . whatever)
       (raise-syntax-error #f "found `<==' outside of the monad"
                           orig-stx stx)]
      [(f x ...)
       (identifier? #'f)
       (+ 1 (for/sum ([x (in-list (syntax->list #'(x ...)))])
                     (count-expr x)))]
      [x
       (or (identifier? #'x)
           (number? (syntax-e #'x)))
       1]))

  (define (check-match-pattern stx)
    (syntax-case stx (nil bt_mt CT_leaf true false)
      [nil
       (raise-syntax-error #f "nil needs parens in a pattern position"
                           orig-stx stx)]
      [bt_mt
       (raise-syntax-error #f "bt_mt needs parens in a pattern position"
                           orig-stx stx)]
      [CT_leaf
       (raise-syntax-error #f "CT_leaf needs parens in a pattern position"
                           orig-stx stx)]
      [true
       (raise-syntax-error #f "true needs parens in a pattern position"
                           orig-stx stx)]
      [false
       (raise-syntax-error #f "false needs parens in a pattern position"
                           orig-stx stx)]
      [(id1 id2 ...)
       (and (identifier? #'id1)
            (andmap identifier? (syntax->list #'(id2 ...))))
       (void)]
      [id
       (identifier? #'id)]
      [_
       (raise-syntax-error #f "malformed pattern" orig-stx stx)]))

  (define (add+= n e)
    (cond
      [(zero? n) e]
      [else #`(+= #,n #,e)]))

  (in-monad 0 orig-stx))

(define-syntax-rule
  (+= k exp)
  (let-values ([(val time) exp])
    (values val (+ time k))))

(define-syntax-rule
  (<== e)
  (values e 0))

(define-syntax-rule
  (bind ([x e]) b)
  (let-values ([(x time) e])
    (let-values ([(r time2) b])
      (values r (+ time time2)))))

(define-syntax (match stx)
  (syntax-case stx (=>)
    [(_ (expr ...) [test1 test2 ... => body] ...)
     #`(r:match*/derived (expr ...) #,stx [(test1 test2 ...) body] ...)]))

(struct bt_mt-struct () #:transparent
        #:methods gen:custom-write
        [(define (write-proc val port mode)
           (display "bt_mt" port))])

(define the-bt_mt (bt_mt-struct))

(struct CT_leaf-struct () #:transparent
        #:methods gen:custom-write
        [(define (write-proc val port mode)
           (display "CT_leaf" port))])

(define the-CT_leaf (CT_leaf-struct))

(struct bt_node (val left right) #:transparent)
(struct CT_node (left color val right) #:transparent)

(r:define-match-expander nil (λ (stx) #''()) (λ (stx) #''()))
(r:define-match-expander bt_mt (λ (stx) #'(bt_mt-struct)) (λ (stx) #'the-bt_mt))
(r:define-match-expander CT_leaf (λ (stx) #'(CT_leaf-struct)) (λ (stx) #'the-CT_leaf))
(r:define-match-expander true (λ (stx) #'#t) (λ (stx) #'#t))
(r:define-match-expander false (λ (stx) #'#f) (λ (stx) #'#f))

(struct BLACK-struct () #:transparent
        #:methods gen:custom-write
        [(define (write-proc val port mode)
           (display "BLACK" port))])
(define the-BLACK (BLACK-struct))
(r:define-match-expander BLACK (λ (stx) #'(BLACK-struct)) (λ (stx) #'the-BLACK))
(struct RED-struct () #:transparent
        #:methods gen:custom-write
        [(define (write-proc val port mode)
           (display "RED" port))])
(define the-RED (RED-struct))
(r:define-match-expander RED (λ (stx) #'(RED-struct)) (λ (stx) #'the-RED))

(r:define-match-expander S 
                         (λ (stx) 
                           (syntax-case stx ()
                             [(_ n)
                              (identifier? #'n)
                              #'(? exact-positive-integer? (app sub1 n))]))
                         (λ (stx)
                           (syntax-case stx ()
                             [(_ n) #'(add1 n)]
                             [x
                              (identifier? #'x)
                              #'add1])))

(struct pair (l r) #:transparent)
(struct left (val) #:transparent)
(struct right (val) #:transparent)

(define (even_odd_dec n) (even? n))
(define (even_oddb n) (even? n))
(define (le_lt_dec n m) (if (<= n m) (left #f) (right #f)))
(define (div2 n) (floor (/ n 2)))
(define (fst p) (pair-l p))
(define (snd p) (pair-r p))

(define (-:nat n m) 
  (define ans (- n m))
  (when (negative? ans)
    (error '- "negative result, ~a - ~a = ~a" n m ans))
  ans)
(define (pred n) (-:nat n 1))
(define (double n) (* n 2))
(define (double_plus1 n) (+ 1 (* n 2)))

;(define false #f)
;(define true #t)
(define-syntax-rule (andb a b) (and a b))
(define-syntax-rule (orb a b) (or a b))
(define (xorb a b) (not (equal? a b)))
(define (negb a) (not a))
