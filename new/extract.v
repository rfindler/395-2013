Require Import insert copy size array Arith.Div2 Arith.Even.

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

Extraction "braun.ml" insert.insert copy.copy size.size_linear size.size array.make_array_linear.
