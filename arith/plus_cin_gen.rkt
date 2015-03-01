#lang at-exp s-exp tmonad

(Fixpoint
 plus_cin @n{nat} @m{nat} @cin{bool}
 #:measure "(m+n)"
 #:returns @{nat}
 (match (n)
   [0 
    => 
    (match (m)
      [0 => (if cin (<== 1) (<== 0))]
      [(S m′)
       => 
       (bind ((ndiv2plusm (plus_cin 0
                                    (div2 m)
                                    (andb cin
                                          (negb (even_oddb m))))))
             (if (xorb (even_oddb m)
                       cin)
                 (<== (double ndiv2plusm))
                 (<== (double_plus_one ndiv2plusm))))])]
   [(S n′)
    =>
    (match (m)
      [0 
       => 
       (bind ((ndiv2plusm (plus_cin (div2 n)
                                    0
                                    (andb cin
                                          (negb (even_oddb n))))))
             (if (xorb (even_oddb n)
                       cin)
                 (<== (double ndiv2plusm))
                 (<== (double_plus_one ndiv2plusm))))]
      [(S m′)
       =>
       (bind ((ndiv2plusm (plus_cin (div2 n)
                                    (div2 m)
                                    (orb (andb (negb (even_oddb n))
                                               (negb (even_oddb m)))
                                         (andb cin
                                               (xorb (even_oddb n)
                                                     (even_oddb m)))))))
             (if (xorb (xorb (even_oddb n)
                             (even_oddb m))
                       cin)
                 (<== (double_plus_one ndiv2plusm))
                 (<== (double ndiv2plusm))))])]))
