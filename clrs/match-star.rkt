#lang racket/base
(require racket/match)

(define (do-match* stx)
  (match-define `(match* #:else ,else ,pat ...) stx)
  (do-match*-inner else pat))

(define (ok-pats id pat pats)
  (map (ok-pat id pat) pats))
(define ((ok-pat id pat) this)
  (match this
    [`[#:ret ,body] this]
    [`[{,id0 ,pat0} ,pats ... #:ret ,body]
     (if (equal? id id0)
         `[,@pats #:ret ,body]
         this)]))

(define (bad-pats id pat pats)
  (filter (bad-pat id pat) pats))
(define ((bad-pat id pat) this)
  (match this
    [`[#:ret ,body] #t]
    [`[{,id0 ,pat0} ,pats ... #:ret ,body]
     (if (equal? id id0) #f #t)]))

(define ID 0)
(define DEFNS (make-hasheq))
(define MEMO (make-hash))
(define (do-match*-inner else pats)
  (hash-ref!
   MEMO pats
   (λ ()
     (match pats
       ['() `(<== ,else)]
       [(cons `[#:ret ,top-body] pats)
        `(<== ,top-body)]
       [(cons `[{,id0 ,pat0} ,top-pats ... #:ret ,top-body] pats)
        (define new-ok-pats
          (cons `[,@top-pats #:ret ,top-body]
                (ok-pats id0 pat0 pats)))
        (define new-bad-pats
          (bad-pats id0 pat0 pats))
        `(match (,id0)
          [,pat0 => ,(do-match*-inner else new-ok-pats)]
          [_ => ,(do-match*-inner else new-bad-pats)])]))))

(module+ test
  (define t
    `(match* #:else (CT_node tl tc tv tr)
      [{tc (BLACK)} {tl (CT_node tll tlc tlv tlr)} {tlc (RED)}
       {tll (CT_node tlll tllc tllv tllr)} {tllc (RED)}
       #:ret
       (CT_node (CT_node tlll BLACK tllv tllr) RED tlv (CT_node tlr BLACK tv tr))]

      [{tc (BLACK)} {tl (CT_node tll tlc tlv tlr)} {tlc (RED)}
       {tlr (CT_node tlrl tlrc tlrv tlrr)} {tlrc (RED)}
       #:ret
       (CT_node (CT_node tll BLACK tlv tlrl) RED tlrv (CT_node tlrr BLACK tv tr))]

      [{tc (BLACK)} {tr (CT_node trl trc trv trr)} {trc (RED)}
       {trl (CT_node trll trlc trlv trlr)} {trlc (RED)}
       #:ret
       (CT_node (CT_node tl BLACK tv trll) RED trlv (CT_node trlr BLACK trv trr))]

      [{tc (BLACK)} {tr (CT_node trl trc trv trr)} {trc (RED)}
       {trr (CT_node trrl trrc trrv trrr)} {trrc (RED)}
       #:ret
       (CT_node (CT_node tl BLACK tv trl) RED trv (CT_node trrl BLACK trrv trrr))]))
  (require racket/pretty)
  (pretty-print (do-match* t))
  (pretty-print DEFNS))
