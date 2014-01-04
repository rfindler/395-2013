Require Import Arith.Div2 Arith.Even.
Require Import Braun.logical.insert Braun.logical.copy Braun.logical.size Braun.logical.index Braun.logical.make_array_naive Braun.logical.make_array_td.

Extract Inductive bool => "bool" [ "false" "true" ].
Extract Inductive sumbool => "bool" [ "false" "true" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => 
"int" [ "0" "succ" ]
      "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "fun x y -> x + y".
Extract Constant mult => "fun x y -> x * y".

Extract Constant div2 => "fun a -> a / 2".
Extract Constant even_odd_dec => "fun a -> (a mod 2) != 0".

Extraction "logical.ml" insert.insert copy.copy size.size_linear
           size.size index.index make_array_naive.make_array_naive
           make_array_td.make_array_td.
