#lang at-exp s-exp tmonad
(provide rbt_balance)

(Fixpoint
 rbt_balance #:implicit @A{Set}
 @tl{CTree A} @tc{Color} @tv{A} @tr{CTree A}
 #:returns @{CTree A}
 (match
  (tc)
  ((BLACK)
   =>
   (match
    (tl)
    ((CT_node tll tlc tlv tlr)
     =>
     (match
      (tlc)
      ((RED)
       =>
       (match
        (tll)
        ((CT_node tlll tllc tllv tllr)
         =>
         (match
          (tllc)
          ((RED)
           =>
           (<==
            (CT_node
             (CT_node tlll BLACK tllv tllr)
             RED
             tlv
             (CT_node tlr BLACK tv tr))))
          (_
           =>
           (match
            (tlr)
            ((CT_node tlrl tlrc tlrv tlrr)
             =>
             (match
              (tlrc)
              ((RED)
               =>
               (<==
                (CT_node
                 (CT_node tll BLACK tlv tlrl)
                 RED
                 tlrv
                 (CT_node tlrr BLACK tv tr))))
              (_
               =>
               (match
                (tr)
                ((CT_node trl trc trv trr)
                 =>
                 (match
                  (trc)
                  ((RED)
                   =>
                   (match
                    (trl)
                    ((CT_node trll trlc trlv trlr)
                     =>
                     (match
                      (trlc)
                      ((RED)
                       =>
                       (<==
                        (CT_node
                         (CT_node tl BLACK tv trll)
                         RED
                         trlv
                         (CT_node trlr BLACK trv trr))))
                      (_
                       =>
                       (match
                        (trr)
                        ((CT_node trrl trrc trrv trrr)
                         =>
                         (match
                          (trrc)
                          ((RED)
                           =>
                           (<==
                            (CT_node
                             (CT_node tl BLACK tv trl)
                             RED
                             trv
                             (CT_node trrl BLACK trrv trrr))))
                          (_ => (<== (CT_node tl tc tv tr)))))
                        (_ => (<== (CT_node tl tc tv tr)))))))
                    (_
                     =>
                     (match
                      (trr)
                      ((CT_node trrl trrc trrv trrr)
                       =>
                       (match
                        (trrc)
                        ((RED)
                         =>
                         (<==
                          (CT_node
                           (CT_node tl BLACK tv trl)
                           RED
                           trv
                           (CT_node trrl BLACK trrv trrr))))
                        (_ => (<== (CT_node tl tc tv tr)))))
                      (_ => (<== (CT_node tl tc tv tr)))))))
                  (_ => (<== (CT_node tl tc tv tr)))))
                (_ => (<== (CT_node tl tc tv tr)))))))
            (_
             =>
             (match
              (tr)
              ((CT_node trl trc trv trr)
               =>
               (match
                (trc)
                ((RED)
                 =>
                 (match
                  (trl)
                  ((CT_node trll trlc trlv trlr)
                   =>
                   (match
                    (trlc)
                    ((RED)
                     =>
                     (<==
                      (CT_node
                       (CT_node tl BLACK tv trll)
                       RED
                       trlv
                       (CT_node trlr BLACK trv trr))))
                    (_
                     =>
                     (match
                      (trr)
                      ((CT_node trrl trrc trrv trrr)
                       =>
                       (match
                        (trrc)
                        ((RED)
                         =>
                         (<==
                          (CT_node
                           (CT_node tl BLACK tv trl)
                           RED
                           trv
                           (CT_node trrl BLACK trrv trrr))))
                        (_ => (<== (CT_node tl tc tv tr)))))
                      (_ => (<== (CT_node tl tc tv tr)))))))
                  (_
                   =>
                   (match
                    (trr)
                    ((CT_node trrl trrc trrv trrr)
                     =>
                     (match
                      (trrc)
                      ((RED)
                       =>
                       (<==
                        (CT_node
                         (CT_node tl BLACK tv trl)
                         RED
                         trv
                         (CT_node trrl BLACK trrv trrr))))
                      (_ => (<== (CT_node tl tc tv tr)))))
                    (_ => (<== (CT_node tl tc tv tr)))))))
                (_ => (<== (CT_node tl tc tv tr)))))
              (_ => (<== (CT_node tl tc tv tr)))))))))
        (_
         =>
         (match
          (tlr)
          ((CT_node tlrl tlrc tlrv tlrr)
           =>
           (match
            (tlrc)
            ((RED)
             =>
             (<==
              (CT_node
               (CT_node tll BLACK tlv tlrl)
               RED
               tlrv
               (CT_node tlrr BLACK tv tr))))
            (_
             =>
             (match
              (tr)
              ((CT_node trl trc trv trr)
               =>
               (match
                (trc)
                ((RED)
                 =>
                 (match
                  (trl)
                  ((CT_node trll trlc trlv trlr)
                   =>
                   (match
                    (trlc)
                    ((RED)
                     =>
                     (<==
                      (CT_node
                       (CT_node tl BLACK tv trll)
                       RED
                       trlv
                       (CT_node trlr BLACK trv trr))))
                    (_
                     =>
                     (match
                      (trr)
                      ((CT_node trrl trrc trrv trrr)
                       =>
                       (match
                        (trrc)
                        ((RED)
                         =>
                         (<==
                          (CT_node
                           (CT_node tl BLACK tv trl)
                           RED
                           trv
                           (CT_node trrl BLACK trrv trrr))))
                        (_ => (<== (CT_node tl tc tv tr)))))
                      (_ => (<== (CT_node tl tc tv tr)))))))
                  (_
                   =>
                   (match
                    (trr)
                    ((CT_node trrl trrc trrv trrr)
                     =>
                     (match
                      (trrc)
                      ((RED)
                       =>
                       (<==
                        (CT_node
                         (CT_node tl BLACK tv trl)
                         RED
                         trv
                         (CT_node trrl BLACK trrv trrr))))
                      (_ => (<== (CT_node tl tc tv tr)))))
                    (_ => (<== (CT_node tl tc tv tr)))))))
                (_ => (<== (CT_node tl tc tv tr)))))
              (_ => (<== (CT_node tl tc tv tr)))))))
          (_
           =>
           (match
            (tr)
            ((CT_node trl trc trv trr)
             =>
             (match
              (trc)
              ((RED)
               =>
               (match
                (trl)
                ((CT_node trll trlc trlv trlr)
                 =>
                 (match
                  (trlc)
                  ((RED)
                   =>
                   (<==
                    (CT_node
                     (CT_node tl BLACK tv trll)
                     RED
                     trlv
                     (CT_node trlr BLACK trv trr))))
                  (_
                   =>
                   (match
                    (trr)
                    ((CT_node trrl trrc trrv trrr)
                     =>
                     (match
                      (trrc)
                      ((RED)
                       =>
                       (<==
                        (CT_node
                         (CT_node tl BLACK tv trl)
                         RED
                         trv
                         (CT_node trrl BLACK trrv trrr))))
                      (_ => (<== (CT_node tl tc tv tr)))))
                    (_ => (<== (CT_node tl tc tv tr)))))))
                (_
                 =>
                 (match
                  (trr)
                  ((CT_node trrl trrc trrv trrr)
                   =>
                   (match
                    (trrc)
                    ((RED)
                     =>
                     (<==
                      (CT_node
                       (CT_node tl BLACK tv trl)
                       RED
                       trv
                       (CT_node trrl BLACK trrv trrr))))
                    (_ => (<== (CT_node tl tc tv tr)))))
                  (_ => (<== (CT_node tl tc tv tr)))))))
              (_ => (<== (CT_node tl tc tv tr)))))
            (_ => (<== (CT_node tl tc tv tr)))))))))
      (_
       =>
       (match
        (tr)
        ((CT_node trl trc trv trr)
         =>
         (match
          (trc)
          ((RED)
           =>
           (match
            (trl)
            ((CT_node trll trlc trlv trlr)
             =>
             (match
              (trlc)
              ((RED)
               =>
               (<==
                (CT_node
                 (CT_node tl BLACK tv trll)
                 RED
                 trlv
                 (CT_node trlr BLACK trv trr))))
              (_
               =>
               (match
                (trr)
                ((CT_node trrl trrc trrv trrr)
                 =>
                 (match
                  (trrc)
                  ((RED)
                   =>
                   (<==
                    (CT_node
                     (CT_node tl BLACK tv trl)
                     RED
                     trv
                     (CT_node trrl BLACK trrv trrr))))
                  (_ => (<== (CT_node tl tc tv tr)))))
                (_ => (<== (CT_node tl tc tv tr)))))))
            (_
             =>
             (match
              (trr)
              ((CT_node trrl trrc trrv trrr)
               =>
               (match
                (trrc)
                ((RED)
                 =>
                 (<==
                  (CT_node
                   (CT_node tl BLACK tv trl)
                   RED
                   trv
                   (CT_node trrl BLACK trrv trrr))))
                (_ => (<== (CT_node tl tc tv tr)))))
              (_ => (<== (CT_node tl tc tv tr)))))))
          (_ => (<== (CT_node tl tc tv tr)))))
        (_ => (<== (CT_node tl tc tv tr)))))))
    (_
     =>
     (match
      (tr)
      ((CT_node trl trc trv trr)
       =>
       (match
        (trc)
        ((RED)
         =>
         (match
          (trl)
          ((CT_node trll trlc trlv trlr)
           =>
           (match
            (trlc)
            ((RED)
             =>
             (<==
              (CT_node
               (CT_node tl BLACK tv trll)
               RED
               trlv
               (CT_node trlr BLACK trv trr))))
            (_
             =>
             (match
              (trr)
              ((CT_node trrl trrc trrv trrr)
               =>
               (match
                (trrc)
                ((RED)
                 =>
                 (<==
                  (CT_node
                   (CT_node tl BLACK tv trl)
                   RED
                   trv
                   (CT_node trrl BLACK trrv trrr))))
                (_ => (<== (CT_node tl tc tv tr)))))
              (_ => (<== (CT_node tl tc tv tr)))))))
          (_
           =>
           (match
            (trr)
            ((CT_node trrl trrc trrv trrr)
             =>
             (match
              (trrc)
              ((RED)
               =>
               (<==
                (CT_node
                 (CT_node tl BLACK tv trl)
                 RED
                 trv
                 (CT_node trrl BLACK trrv trrr))))
              (_ => (<== (CT_node tl tc tv tr)))))
            (_ => (<== (CT_node tl tc tv tr)))))))
        (_ => (<== (CT_node tl tc tv tr)))))
      (_ => (<== (CT_node tl tc tv tr)))))))
  (_ => (<== (CT_node tl tc tv tr)))))
