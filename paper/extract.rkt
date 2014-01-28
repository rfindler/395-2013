#lang racket/base

(provide extract)

(define (extract fn tag)
  (call-with-input-file fn
    (λ (port)
      (let loop ()
        (define l (read-line port))
        (cond
          [(eof-object? l) 
           (error 'extract "didn't find start ~a tag in ~a" tag fn)]
          [(matches-start? tag l) (void)]
          [else (loop)]))
      (define lines
        (let loop ()
          (define l (read-line port))
          (cond
            [(eof-object? l) 
             (error 'extract "didn't find end ~a tag in ~a" tag fn)]
            [(matches-end? tag l) '()]
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
