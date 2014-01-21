#lang racket/base

(require (for-syntax racket/match racket/base)
         racket/contract
         (prefix-in r: racket/match))

(provide (rename-out [module-begin #%module-begin]
                     [top-interaction #%top-interaction])
         #%datum
         #%app
         Fixpoint
         bt_mt
         bt_node
         match bind let => <==
         provide
         require
         cons
         nil
         pair)


(define-syntax (top-interaction stx)
  (syntax-case stx ()
    [(_ . e)
     (let ()
       (define converted (add-plusses #'e))
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
                       (list #'Fixpoint #'provide #'require))
                arg]
               [_ #`(top-interaction . #,arg)])))]))

(define-for-syntax (nmid? x)
  (and (identifier? x)
       (member x (syntax->list #'(pair bt_node cons)) free-identifier=?)))

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

(define-syntax (Fixpoint stx)
  (syntax-case stx ()
    [(_ id args ... body)
     (begin
       (unless (identifier? #'id)
         (raise-syntax-error 'Fixpoint "expected identifier"
                             stx #'id))
       (define-values (racket-args coq-args coq-result)
         (parse-Fixpoint-args stx #'(args ...)))
       (define exp (add-plusses #'body))
       #`(begin 
           (module+ main
             (require "emit.rkt")
             (out-Fp (Fp 'id (list #,@coq-args) #,coq-result '#,exp)))
           (define (id #,@racket-args) #,exp)))]))

;; expects an anormalized <exp> as input
;; returns something with ret and inc annotations
;; (the lets are already the right binds)

(define-for-syntax (add-plusses orig-stx)
  (define (in-monad stx)
    (syntax-case stx (match if bind => <==)
      [(match t [ps => es] ...)
       ;; destructuring matches are free
       (let ([inc (if (= 1 (length (syntax->list #'(ps ...)))) 0 1)])
         (with-syntax ([(mes ...) (for/list ([e (in-list (syntax->list #'(es ...)))])
                                    (in-monad e))])
           (add+= (+ inc (count-expr #'t))
                  #`(match t [ps => mes] ...))))]
      [(if tst thn els)
       (add+= (+ 1 (count-expr #'tst))
              #`(if tst #,(in-monad #'thn) #,(in-monad #'els)))]
      [(bind ([x rhs]) body)
       (add+= 1 #`(bind ([x #,(in-monad #'rhs)]) #,(in-monad #'body)))]
      [(f x ...)
       (nmid? #'f)
       (raise-syntax-error #f "non-monad returning function in a monad place" orig-stx #'f)]
      [(<== e)
       (add+= (count-expr #'e) stx)]
      [(f x ...)
       (identifier? #'f)
       (let ()
         (define extra
           (for/sum ([e (in-list (syntax->list #'(x ...)))])
             (count-expr e)))
         (add+= (+ extra 1) stx))]))
  
  (define (count-expr stx)
    (syntax-case stx (match if bind => <==)
      [(match . whatever)
       (raise-syntax-error #f "cannot count a `match' outside of the monad" orig-stx stx)]
      [(if . whatever)
       (raise-syntax-error #f "cannot count an `if' outside of the monad" orig-stx stx)]
      [(bind . whatever)
       (raise-syntax-error #f "found `bind' outside of the monad" orig-stx stx)]
      [(<== . whatever)
       (raise-syntax-error #f "found `<==' outside of the monad" orig-stx stx)]
      [(f x ...)
       (identifier? #'f)
       (+ 1 (for/sum ([x (in-list (syntax->list #'(x ...)))])
              (count-expr x)))]
      [x
       (or (identifier? #'x)
           (number? (syntax-e #'x)))
       1]))
  
  (define (add+= n e)
    (cond
      [(zero? n) e]
      [else #`(+= #,n #,e)]))
  
  (in-monad orig-stx))

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
    [(_ expr [test => body] ...)
     #'(let ([x expr])
         (r:match x [test body] ...))]))

(struct bt_mt-struct () #:transparent
  #:methods gen:custom-write
  [(define (write-proc val port mode)
     (display "bt_mt" port))])

(define the-bt_mt (bt_mt-struct))

(struct bt_node (val left right) #:transparent)

(r:define-match-expander nil (λ (stx) #''()) (λ (stx) #''()))
(r:define-match-expander bt_mt (λ (stx) #'(bt_mt-struct)) (λ (stx) #'the-bt_mt))

(struct pair (l r) #:transparent)
