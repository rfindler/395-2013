#lang at-exp racket/base
(require racket/runtime-path
         racket/list
         scribble/base)
(define-runtime-path above "..")
(provide build-table)

;; classification:
;;  (listof <dir>)
;;  <dir> = (cons/c string?[dirname] (listof <problem>))
;;  <problem> = (cons/c <main-file> (listof <file>))
(define classification
  '(("size"
     ("size_linear.v" "size_linear_gen.v")
     ("size_log_sq.v" "diff_gen.v" "size_log_sq_gen.v"))
    ("copy"
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
      "build.v" "build_gen.v"))))

(define (build-table)
  (define info (collect-info))
  (define one-line-per-file
    (apply append
           (add-between (apply append info) (list #f))))
  
  (define (get-total sel)
    (format "~a"
            (for/sum ([x (in-list one-line-per-file)])
              (cond
                [(pair? x)
                 (sel (cdr x))]
                [else 0]))))
  (define blank-row (list "" 'cont 'cont 'cont))
  (tabular
   #:sep @hspace[1]
   (append
    (list
     (list @bold{File} 
           @bold{Non-whitespace Lines}
           @bold{Obligation Lines}
           @bold{Other Proof Lines})
     blank-row)
    (for/list ([row (in-list one-line-per-file)])
      (cond
        [row
         (define inf (cdr row))
         (list @tt{@(car row)}
               (format "~a" (line-info-total inf))
               (format "~a" (line-info-obligations inf))
               (format "~a" (line-info-proofs inf)))]
        [else blank-row]))
    (list (list @bold{Total} 
                (get-total line-info-total)
                (get-total line-info-obligations)
                (get-total line-info-proofs))))))
      
(define (collect-info)
  (for/list ([dir-list (in-list classification)])
    (define dir (list-ref dir-list 0))
    (define all-files 
      (filter (λ (x) (regexp-match #rx"[.]v$" x))
              (map path->string (directory-list (build-path above dir)))))
    (define line-infos
      (for/list ([problem (in-list (cdr dir-list))])
        (for/list ([file (in-list problem)])
          (set! all-files (remove file all-files))
          (cons file (parse-file (build-path dir file))))))
    (unless (null? all-files)
      (eprintf "~a has ~a, not mentioned\n\n"
               dir all-files))
    line-infos))

(struct line-info (proofs obligations total) #:transparent)

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
          (fail "Didn't find Proof. line for Qed.")))
      
      (define (fail msg)
        (define-values (line col pos) (port-next-location port))
        (error 'parse-file "~a on line ~a of ~a"
               msg
               (- line 1)
               fn))
      
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
              (when (regexp-match #rx"Qed[.]" line)
                (fail "found Qed. on same line as Proof."))
              (set! found-proof-line? #t)
              (set! line-counter 0)]
             [(regexp-match #rx"Qed[.]" line)
              (finish-proof)
              (set! in-obligation? #f)
              (set! found-proof-line? #f)]
             [else
              (set! line-counter (+ line-counter 1))])]))
      
      (line-info proof-line-count obligation-line-count total-line-count))))

(module+ main (void (collect-info)))
