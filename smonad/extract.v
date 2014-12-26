Require Import Braun.smonad.smonad.
Require Import Braun.smonad.snoc.
Require Import Braun.smonad.reverse.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "false" "true" ].
Extract Inductive sumbool => "bool" [ "false" "true" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive nat => 
"int" [ "0" "succ" ]
      "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Constant plus => "fun x y -> x + y".
Extract Constant mult => "fun x y -> x * y".
Extract Constant minus => "fun x y -> x - y".

Extraction Inline ret bind inc get put weaken.
Extraction Inline projT1 projT2.

Extraction "sextract.ml" store_snoc memory_list_of_len.
