#lang racket/base
(require racket/contract)

(provide
 (contract-out
  [extract (-> path-string?
               (or/c string?
                     (-> (listof string?) (listof string?)))
               (listof string?))]))

(define (extract fn tag-or-fun)
  (call-with-input-file fn
    (λ (port)
      (let loop ()
        (define l (read-line port))
        (cond
          [(eof-object? l) 
           (error 'extract "didn't find start ~a tag in ~a" tag-or-fun fn)]
          [(if (string? tag-or-fun)
               (matches-start? tag-or-fun l)
               #t)
           (void)]
          [else (loop)]))
      (define lines
        (let loop ()
          (define l (read-line port))
          (cond
            [(eof-object? l) 
             (if (string? tag-or-fun)
                 (error 'extract "didn't find end ~a tag in ~a" tag-or-fun fn)
                 '())]
            [(if (string? tag-or-fun)
                 (matches-end? tag-or-fun l)
                 #f)
             '()]
            [else (cons l (loop))])))
      (define prefix-len
        (for/fold ([s #f]) ([l (in-list lines)])
          (define prefix (string-length (car (regexp-match #rx"^ *" l))))
          (if s
              (min s prefix)
              prefix)))
      (and prefix-len
           (for/list ([l (in-list lines)])
             (string-append (substring l prefix-len (string-length l))
                            "\n"))))))
           
(define (matches-start? tag line)
  (define m (regexp-match #rx" *[(] *[*] *START: +([^ ]*)" line))
  (and m (equal? (cadr m) tag)))

(define (matches-end? tag line)
  (define m (regexp-match #rx" *[(] *[*] *STOP: +([^ ]*)" line))
  (and m (equal? (cadr m) tag)))
