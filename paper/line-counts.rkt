#lang at-exp racket/base
(require racket/runtime-path
         racket/list
         scribble/base
         racket/format
         racket/contract)
(define-runtime-path above "..")
(provide build-table)

;; classification:
;;  (listof <dir>)
;;  <dir> = (cons/c string?[dirname] (listof <problem>))
;;  <problem> = (cons/c <main-file> (listof <file>))
(define braun-tree-classification
  '(("copy"
     ("copy_linear.v" "copy_linear_gen.v")
     ("copy_fib_log.v" "copy_fib_log_gen.v")
     ("copy_log_sq.v" "copy_log_sq_gen.v")
     ("copy_log.v" "copy_log_gen.v" "copy2_gen.v"))
    ("make_array"
     ("make_array_nlogn1.v" "make_array_nlogn1_gen.v")
     ("make_array_nlogn1_fold.v")
     ("make_array_nlogn2.v" "make_array_nlogn2_gen.v" "unravel_gen.v")
     ("make_array_linear.v" "make_array_linear_gen.v"
      "rows.v" "rows1_gen.v" "rows_gen.v"
      "take_drop_split.v" "drop_gen.v" "take_gen.v" "pad_drop_gen.v" "split_gen.v"
      "foldr_build_gen.v"
      "zip_with_3_bt_node_gen.v"
      "build.v" "build_gen.v"))
    ("to_list"
     ("to_list_naive.v" "cinterleave_gen.v" "to_list_naive_gen.v"))))

(define other-classification 
  '(("clrs"
     ("rbtree.v"
      "rbt_search.v"
      "bst_search_gen.v")
     ("rbt_insert.v"
      "rbt_balance_gen.v"
      "rbt_blacken_gen.v"
      "rbt_insert_gen.v"
      "rbt_insert_inner_gen.v"))
    ("sort"
     ("sorting.v")
     ("isort.v"
      "insert_gen.v"
      "isort_gen.v")
     ("merge_gen.v"
      "mergesort.v"
      "mergesort_gen.v"
      "mergesortc_gen.v"
      "split2_gen.v"
      "clength_gen.v"))
    ("fib"
     ("fib.v" 
      "fib_iter_gen.v"
      "fib_iter_loop_gen.v"
      "fib_rec_gen.v"))
    ("size"
     ("size_linear.v" "size_linear_gen.v")
     ("size_log_sq.v" "diff_gen.v" "size_log_sq_gen.v"))
    ("clrs"
     ("zip.v" "from_zip_gen.v" "minsert_at_gen.v" "minsertz_at_gen.v"
      "to_zip_gen.v" "zip_insert_gen.v" "zip_left_gen.v" "zip_leftn_gen.v"
      "zip_minsert_gen.v" "zip_right_gen.v" "zip_rightn_gen.v"))))

(define (build-table)
  (tabular
   #:sep @hspace[6]
   (list (list (build-one-side-of-table other-classification #f)
               (build-one-side-of-table braun-tree-classification #t)))))

(define (count-a-dir dir)
  (compute-subtotal
   (for/list ([fn (in-list (directory-list (build-path above dir)))]
              #:when (regexp-match #rx"[.]v$" (path->string fn)))
     (cons fn (parse-file (build-path dir fn))))))

(struct line-info (proofs obligations non-proofs) #:transparent)

(define (build-one-side-of-table classification total?)
  (define info (collect-info classification))
  (define one-line-per-file
    (apply append
           (apply append info)))
  (define blank-row (list "" 'cont 'cont 'cont))
  (define (make-a-row label info)
    (list @bold{@label} 
          (format-number (line-info-non-proofs info))
          (format-number (line-info-obligations info))
          (format-number (line-info-proofs info))))
  (define common-lines 
    (list (cons 'Monad (count-a-dir "monad"))
          (cons 'Common (count-a-dir "common"))))
  (define all-rows 
    (append one-line-per-file common-lines))
  (define (build-table-row row)
    (cond
      [row
       (define label (car row))
       (define inf (cdr row))
       (list (if (symbol? label)
                 @bold{@(format "~a" label)}
                 @tt{@(car row)})
             (format-number (line-info-non-proofs inf))
             (format-number (line-info-obligations inf))
             (format-number (line-info-proofs inf)))]
      [else blank-row]))
  (tabular
   #:sep @hspace[1]
   (append
    (list
     (list @bold{File} 
           @bold{Non-}
           @bold{Obligation}
           @bold{Other})
     (list @bold{} 
           @bold{Proof}
           @bold{Lines}
           @bold{Proof})
     (list @bold{} 
           @bold{Lines}
           @bold{}
           @bold{Lines}))
    (for/list ([row (in-list one-line-per-file)])
      (build-table-row row))
    (list blank-row)
    
    (if total?
        (list (list @bold{Totals}
                    (format-number (get-total all-rows line-info-non-proofs))
                    (format-number (get-total all-rows line-info-obligations))
                    (format-number (get-total all-rows line-info-proofs)))
              (list (list @bold{Total number of lines:})
                    (list (format-number (+ (get-total all-rows line-info-non-proofs)
                                            (get-total all-rows line-info-obligations)
                                            (get-total all-rows line-info-proofs))))
                    'cont 'cont))
        (append (for/list ([row (in-list common-lines)])
                  (build-table-row row))
                (list blank-row blank-row))))))

(define/contract (get-total one-line-per-file sel)
  (-> (listof (or/c (cons/c any/c line-info?) #f)) any/c any/c)
  (for/sum ([x (in-list one-line-per-file)])
    (cond
      [(pair? x)
       (sel (cdr x))]
      [else 0])))
      
(define (collect-info classification)
  (for/list ([dir-list (in-list classification)])
    (define dir (list-ref dir-list 0))
    (define all-files 
      (filter (λ (x) (regexp-match #rx"[.]v$" x))
              (map path->string (directory-list (build-path above dir)))))
    (define line-infos
      (for/list ([problem (in-list (cdr dir-list))])
        (define problem-lines
          (for/list ([file (in-list problem)])
            (set! all-files (remove file all-files))
            (cons file (parse-file (build-path dir file)))))
        (define subtotal-line (compute-subtotal problem-lines))
        (append problem-lines
                (list (cons 'Subtotal subtotal-line)))))
    (unless (null? all-files)
      (eprintf "~a has ~a, not mentioned\n\n"
               dir all-files))
    line-infos))

(define (compute-subtotal line-infos)
  (line-info (get-total line-infos line-info-proofs)
             (get-total line-infos line-info-obligations)
             (get-total line-infos line-info-non-proofs)))

(define (format-number n)
  (cond
    [(< n 1000) (format "~a" n)]
    [(< n 1000000) (format "~a,~a" (quotient n 1000) 
                           (~a (modulo n 1000)
                               #:pad-string "0"
                               #:min-width 3))]
    [else (error 'format-number "too big")]))

(module+ test 
  (require rackunit)
  (check-equal? (format-number 0) "0")
  (check-equal? (format-number 10) "10")
  (check-equal? (format-number 100) "100")
  (check-equal? (format-number 1000) "1,000")
  (check-equal? (format-number 10000) "10,000")
  (check-equal? (format-number 100000) "100,000")
  (check-equal? (format-number 123456) "123,456"))

(define (parse-file fn)
  (call-with-input-file (build-path above fn)
    (λ (port)
      (port-count-lines! port)
      (define state 'outside)
      (define line-counter 0)
      (define in-obligation? #f)
      
      (define proof-line-count 0)
      (define obligation-line-count 0)
      (define total-line-count 0)
      (define found-proof-line? #f)
      (define (finish-proof)
        (cond
          [in-obligation?
           (set! obligation-line-count (+ obligation-line-count line-counter))]
          [else
           (set! proof-line-count (+ proof-line-count line-counter))])
        (unless found-proof-line?
          (fail "Didn't find Proof. line for Qed. (or Defined.)")))
      
      (define (fail msg)
        (define-values (line col pos) (port-next-location port))
        (error 'parse-file "~a on line ~a of ~a"
               msg
               (- line 1)
               fn))
      
      (define qed-regexp #rx"(Qed[.])|(Defined[.])")
      
      (for ([line (in-lines port)])
        (cond
          [(regexp-match #rx"^[ \t]*$" line)
           (void)]
          [(regexp-match #rx"[(][*].*[*][)]" line)
           (void)]
          [(regexp-match #rx"[(][*]" line)
           (error 'parse-file "multi-line comment in ~a" fn)]
          [else
           (set! total-line-count (+ total-line-count 1))
           (cond
             [(regexp-match #rx"Next Obligation[.]" line)
              (when (regexp-match #rx"Proof[.]" line)
                (fail "found Next Obligation. on same line as Proof."))
              (set! in-obligation? #t)]
             [(regexp-match #rx"Proof[.]" line)
              (when (regexp-match qed-regexp line)
                (fail "found Qed. (or Defined.) on same line as Proof."))
              (set! found-proof-line? #t)
              (set! line-counter 0)]
             [(regexp-match qed-regexp line)
              (finish-proof)
              (set! in-obligation? #f)
              (set! found-proof-line? #f)]
             [else
              (set! line-counter (+ line-counter 1))])]))
      
      (line-info proof-line-count 
                 obligation-line-count 
                 (- total-line-count
                    obligation-line-count
                    proof-line-count)))))

(module+ main 
  (void (build-table)))

