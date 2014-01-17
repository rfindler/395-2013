#lang racket/base

(require (for-syntax racket/match racket/base)
         racket/contract
         (prefix-in r: racket/match))

(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         #%datum
         Fixpoint
         bt_mt
         bt_node
         match if let =>
         provide)


(define-syntax (top-interaction stx)
  (syntax-case stx ()
    [(_ . e)
     (let ()
       (define converted (convert/check #'e))
       #`(let-values ([(val time) #,converted])
           (printf "~a steps\n" time)
           val))]))

(define-syntax (module-begin stx)
  (syntax-case stx ()
    [(_ args ...)
     #`(#%module-begin
        (module+ main (require "emit.rkt") (out-prefix))
        #,@(for/list ([arg (in-list (syntax->list #'(args ...)))])
             (syntax-case arg ()
               [(id . whatever)
                (ormap (λ (x) (free-identifier=? x #'id))
                       (list #'Fixpoint #'provide))
                arg]
               [_ #`(top-interaction . #,arg)])))]))

(define-for-syntax (nmid? x)
  (member x (syntax->list #'(pair bt_node cons)) free-identifier=?))

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
             [coq-args '()])
  (syntax-case args ()
    [(#:implicit arg . args)
     (let ()
       (define-values (racket-arg coq-arg) (parse-Fixpoint-arg stx #'arg #t))
       (loop #'args racket-args (cons coq-arg coq-args)))]
    [(#:returns result)
     (let ()
       (define res-strs (syntax->list #'result))
       (unless res-strs (raise-syntax-error #f "expected a sequence of strings" stx #'result))
       (values (reverse racket-args)
               (reverse coq-args)
               (apply string-append (map syntax-e res-strs))))]
    [(kw . args)
     (keyword? (syntax-e #'kw))
     (raise-syntax-error #f "unexpected keyword" stx #'kw)]
    [(arg . args)
     (let ()
       (define-values (racket-arg coq-arg) (parse-Fixpoint-arg stx #'arg #f))
       (loop #'args (cons racket-arg racket-args) (cons coq-arg coq-args)))]
    [()
     (raise-syntax-error #f "didn't find #:returns keyword" stx)])))

(define-for-syntax (convert/check exp)
  ;;; need to add checking code
  (to-monad (anorm exp)))

(define-syntax (convert/check-exp stx)
  (syntax-case stx ()
    [(_ exp)
     (convert/check #'exp)]))

(define-syntax (Fixpoint stx)
  (syntax-case stx ()
    [(_ id args ... body)
     (begin
       (unless (identifier? #'id)
         (raise-syntax-error 'Fixpoint "expected identifier"
                             stx #'id))
       (define-values (racket-args coq-args coq-result)
         (parse-Fixpoint-args stx #'(args ...)))
       (define exp (convert/check #'body))
       #`(begin 
           (module+ main
             (require "emit.rkt")
             (out-Fp (Fp 'id (list #,@coq-args) #,coq-result '#,exp)))
           (define (id #,@racket-args) #,exp)))]))

(define-for-syntax (anorm exp)
  (struct mtch-ctxt (pats exps k))
  (struct if-ctxt (thn els k))
  (struct let-ctxt (x body k))
  (struct app-ctxt (f before after k))
  
  (define (find exp k)
    (syntax-case exp (=> match if let)
      [(match test [pats => exps] ...)
       (find #'test (mtch-ctxt #'(pats ...) #'(exps ...) k))]
      [(if test thn els)
       (find #'test (if-ctxt #'thn #'els k))]
      [(let ([x rhs]) body)
       (find #'rhs (let-ctxt #'x #'body k))]
      [(f arg1 args ...)
       (find #'arg1 (app-ctxt #'f '() (syntax->list #'(args ...)) k))]
      [_
       (or (identifier? exp)
           (number? (syntax-e exp)))
       (fill exp k)]
      [_
       (error 'find "got bad input: ~s" (syntax->datum exp))]))
  
  (define (fill d k)
    (match k
      [#f 
       ;; we could just return 'd' here, but
       ;; we always introduce another 'bind' so 
       ;; that Program has one more place to insert
       ;; invariants
       (maybe-let d (λ (id) id))]
      [(mtch-ctxt pats exps k)
       (maybe-let
        d
        (λ (id)
          (with-syntax ([(f-exps ...) 
                         (for/list ([exp (in-list (syntax->list exps))])
                           (find exp k))]
                        [(pats ...) pats])
          #`(match #,id
              [pats => f-exps] ...))))]
      [(if-ctxt thn els k)
       (maybe-let
        d
        (λ (id)
          #`(if #,id #,(find thn k) #,(find els k))))]
      [(let-ctxt x body k)
       #`(let ([#,x #,d])
           #,(find body x))]
      [(app-ctxt f before '() k)
       (maybe-let 
        d
        (λ (id)
          (fill #`(#,f #,@(reverse before) #,id) k)))]
      [(app-ctxt f before (cons fst rst) k)
       (maybe-let 
        d
        (λ (id)
          (find fst (app-ctxt f (cons id before) rst k))))]))
  
  (define (maybe-let d/x f)
    (cond
      [(or (identifier? d/x)
           (number? (syntax-e d/x)))
       (f d/x)]
      [else
       (with-syntax ([(var) (generate-temporaries '(anorm))])
         #`(let ([var #,d/x])
             #,(f #'var)))]))
  
  (find exp #f))

;; expects an anormalized <exp> as input
;; returns something with ret and inc annotations
;; (the lets are already the right binds)

(define-for-syntax (to-monad exp)
  (let loop ([exp exp]
             [c 0])
    (syntax-case exp (match if let =>)
      [(match t [ps => es] ...)
       ;; destructuring matches are free
       (let ([inc (if (= 1 (length (syntax->list #'(ps ...)))) 0 1)])
         (with-syntax ([(mes ...) (for/list ([e (in-list (syntax->list #'(es ...)))])
                                    (loop e (+ c inc)))])
           #`(match t [ps => mes] ...)))]
      [(if x t e)
       #`(if x #,(loop #'t (+ c 1)) #,(loop #'e (+ c 1)))]
      [(let ([y (f x ...)]) b)
       (with-syntax ([wrapped-app
                      (if (nmid? #'f)
                          #'(<== (f x ...))
                          #'(f x ...))])
         #`(bind ([y wrapped-app])
             #,(loop #'b (+ c 1))))]
      [(f x ...) 
       (if (nmid? #'f)
           #`(++ #,(+ c 1) (<== (f x ...)))
           #`(++ #,(+ c 1) (f x ...)))]
      [x/v
       (or (identifier? #'x/v) (number? (syntax-e #'x/v)))
       #`(++ #,c (<== x/v))])))

(define-syntax-rule
  (++ k exp)
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
    [(_ expr [test => body] ...)
     #'(r:match expr [test body] ...)]))

(define bt_mt 
  (cond
    [else
     (struct bt_mt () #:transparent
       #:methods gen:custom-write
       [(define (write-proc val port mode)
          (display "bt_mt" port))])
     (bt_mt)]))

(struct bt_node (val left right) #:transparent)