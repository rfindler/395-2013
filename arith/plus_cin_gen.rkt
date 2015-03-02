#lang at-exp s-exp tmonad/overly-specific

(require "add1_gen.rkt")

(Fixpoint
 plus_cin @n{nat} @m{nat} @cin{bool}
 #:measure "(m+n)"
 #:returns @{nat}
 (match (n)
   [0
    =>
    (match (m)
      [0 => (match (cin)
              [(true) => (<== 1)]
              [(false) => (<== 0)])]
      [(S m′)
       => 
       (match (cin)
         [(true)
          =>
          (bind ((res (add1 m)))
                (<== res))]
         [(false) => (<== m)])])]
   [(S n′)
    =>
    (match (m)
      [0 
       => 
       (match (cin)
         [(true)
          =>
          (bind ((res (add1 n)))
                (<== res))]
         [(false) => (<== n)])]
      [(S m′)
       =>
       (bind ((ndiv2plusmdiv2plusX
               (plus_cin (div2 n)
                         (div2 m)
                         (orb (andb (negb (even_oddb n))
                                    (negb (even_oddb m)))
                              (andb cin
                                    (xorb (even_oddb n)
                                          (even_oddb m)))))))
             (match ((xorb (xorb (even_oddb n)
                                 (even_oddb m))
                           cin))
               [(true)
                =>
                (<== (double_plus_one ndiv2plusmdiv2plusX))]
               [(false)
                =>
                (<== (double ndiv2plusmdiv2plusX))]))])]))

