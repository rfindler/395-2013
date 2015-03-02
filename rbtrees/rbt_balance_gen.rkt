#lang at-exp s-exp tmonad/overly-specific
(provide rbt_balance)

(Fixpoint
 rbt_balance 
 @A{Set} @tl{CTree A} @tc{Color} @tv{A} @tr{CTree A}
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
             A
             (CT_node A tlll BLACK tllv tllr)
             RED
             tlv
             (CT_node A tlr BLACK tv tr))))
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
                 A
                 (CT_node A tll BLACK tlv tlrl)
                 RED
                 tlrv
                 (CT_node A tlrr BLACK tv tr))))
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
                         A
                         (CT_node A tl BLACK tv trll)
                         RED
                         trlv
                         (CT_node A trlr BLACK trv trr))))
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
                             A
                             (CT_node A tl BLACK tv trl)
                             RED
                             trv
                             (CT_node A trrl BLACK trrv trrr))))
                          (_ => (<== (CT_node A tl tc tv tr)))))
                        (_ => (<== (CT_node A tl tc tv tr)))))))
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
                           A
                           (CT_node A tl BLACK tv trl)
                           RED
                           trv
                           (CT_node A trrl BLACK trrv trrr))))
                        (_ => (<== (CT_node A tl tc tv tr)))))
                      (_ => (<== (CT_node A tl tc tv tr)))))))
                  (_ => (<== (CT_node A tl tc tv tr)))))
                (_ => (<== (CT_node A tl tc tv tr)))))))
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
                       A
                       (CT_node A tl BLACK tv trll)
                       RED
                       trlv
                       (CT_node A trlr BLACK trv trr))))
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
                           A
                           (CT_node A tl BLACK tv trl)
                           RED
                           trv
                           (CT_node A trrl BLACK trrv trrr))))
                        (_ => (<== (CT_node A tl tc tv tr)))))
                      (_ => (<== (CT_node A tl tc tv tr)))))))
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
                         A
                         (CT_node A tl BLACK tv trl)
                         RED
                         trv
                         (CT_node A trrl BLACK trrv trrr))))
                      (_ => (<== (CT_node A tl tc tv tr)))))
                    (_ => (<== (CT_node A tl tc tv tr)))))))
                (_ => (<== (CT_node A tl tc tv tr)))))
              (_ => (<== (CT_node A tl tc tv tr)))))))))
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
               A
               (CT_node A tll BLACK tlv tlrl)
               RED
               tlrv
               (CT_node A tlrr BLACK tv tr))))
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
                       A
                       (CT_node A tl BLACK tv trll)
                       RED
                       trlv
                       (CT_node A trlr BLACK trv trr))))
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
                           A
                           (CT_node A tl BLACK tv trl)
                           RED
                           trv
                           (CT_node A trrl BLACK trrv trrr))))
                        (_ => (<== (CT_node A tl tc tv tr)))))
                      (_ => (<== (CT_node A tl tc tv tr)))))))
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
                         A
                         (CT_node A tl BLACK tv trl)
                         RED
                         trv
                         (CT_node A trrl BLACK trrv trrr))))
                      (_ => (<== (CT_node A tl tc tv tr)))))
                    (_ => (<== (CT_node A tl tc tv tr)))))))
                (_ => (<== (CT_node A tl tc tv tr)))))
              (_ => (<== (CT_node A tl tc tv tr)))))))
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
                     A
                     (CT_node A tl BLACK tv trll)
                     RED
                     trlv
                     (CT_node A trlr BLACK trv trr))))
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
                         A
                         (CT_node A tl BLACK tv trl)
                         RED
                         trv
                         (CT_node A trrl BLACK trrv trrr))))
                      (_ => (<== (CT_node A tl tc tv tr)))))
                    (_ => (<== (CT_node A tl tc tv tr)))))))
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
                       A
                       (CT_node A tl BLACK tv trl)
                       RED
                       trv
                       (CT_node A trrl BLACK trrv trrr))))
                    (_ => (<== (CT_node A tl tc tv tr)))))
                  (_ => (<== (CT_node A tl tc tv tr)))))))
              (_ => (<== (CT_node A tl tc tv tr)))))
            (_ => (<== (CT_node A tl tc tv tr)))))))))
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
                 A
                 (CT_node A tl BLACK tv trll)
                 RED
                 trlv
                 (CT_node A trlr BLACK trv trr))))
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
                     A
                     (CT_node A tl BLACK tv trl)
                     RED
                     trv
                     (CT_node A trrl BLACK trrv trrr))))
                  (_ => (<== (CT_node A tl tc tv tr)))))
                (_ => (<== (CT_node A tl tc tv tr)))))))
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
                   A
                   (CT_node A tl BLACK tv trl)
                   RED
                   trv
                   (CT_node A trrl BLACK trrv trrr))))
                (_ => (<== (CT_node A tl tc tv tr)))))
              (_ => (<== (CT_node A tl tc tv tr)))))))
          (_ => (<== (CT_node A tl tc tv tr)))))
        (_ => (<== (CT_node A tl tc tv tr)))))))
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
               A
               (CT_node A tl BLACK tv trll)
               RED
               trlv
               (CT_node A trlr BLACK trv trr))))
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
                   A
                   (CT_node A tl BLACK tv trl)
                   RED
                   trv
                   (CT_node A trrl BLACK trrv trrr))))
                (_ => (<== (CT_node A tl tc tv tr)))))
              (_ => (<== (CT_node A tl tc tv tr)))))))
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
                 A
                 (CT_node A tl BLACK tv trl)
                 RED
                 trv
                 (CT_node A trrl BLACK trrv trrr))))
              (_ => (<== (CT_node A tl tc tv tr)))))
            (_ => (<== (CT_node A tl tc tv tr)))))))
        (_ => (<== (CT_node A tl tc tv tr)))))
      (_ => (<== (CT_node A tl tc tv tr)))))))
  (_ => (<== (CT_node A tl tc tv tr)))))
