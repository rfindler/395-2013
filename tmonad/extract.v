Require Import Arith.Div2 Arith.Even.
Require Import Braun.tmonad.insert.
Require Import Braun.tmonad.copy Braun.tmonad.copy_linear.
Require Import Braun.tmonad.size Braun.tmonad.size2.
Require Import Braun.tmonad.make_array_naive.
Require Import Braun.tmonad.to_list_naive.
Require Import Braun.tmonad.make_array_td.
Require Import Braun.tmonad.monad.

Extract Inductive bool => "bool" [ "false" "true" ].
Extract Inductive sumbool => "bool" [ "false" "true" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => 
"int" [ "0" "succ" ]
      "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "fun x y -> x + y".
Extract Constant mult => "fun x y -> x * y".
Extract Constant minus => "fun x y -> x - y".

Extract Constant div2 => "fun a -> a / 2".
Extract Constant even_odd_dec => "fun a -> (a mod 2) != 0".

Extraction Inline ret bind inc.

Extraction "tmonad.ml" insert.insert 
           copy.copy copy_linear.copy_linear
           size.size_linear size2.size
           make_array_naive.make_array_naive
           make_array_td.make_array_td
           to_list_naive.to_list_naive.
