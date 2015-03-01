#lang at-exp s-exp tmonad

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
          (match ((even_oddb m))
            [(true)
             =>
             (bind ((mdiv2plusX (plus_cin 0
                                          (div2 m)
                                          false)))
                   (<== (double_plus_one mdiv2plusX)))]
            [(false)
             =>
             (bind ((mdiv2plusX (plus_cin 0
                                          (div2 m)
                                          true)))
                   (<== (double mdiv2plusX)))])]
         [(false) => (<== m)])])]
   [(S n′)
    =>
    (match (m)
      [0 
       => 
       (match (cin)
         [(true)
          =>
          (match ((even_oddb n))
            [(true)
             =>
             (bind ((mdiv2plusX (plus_cin (div2 n)
                                          0
                                          false)))
                   (<== (double_plus_one mdiv2plusX)))]
            [(false)
             =>
             (bind ((mdiv2plusX (plus_cin (div2 n)
                                          0
                                          true)))
                   (<== (double mdiv2plusX)))])]
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
