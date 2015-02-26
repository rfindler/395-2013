Require Import Arith.Div2 Arith.Even.

Require Import Braun.insert.insert_log.

Require Import Braun.copy.copy_linear Braun.copy.copy_fib_log.
Require Import Braun.copy.copy_log_sq Braun.copy.copy_log.

Require Import Braun.size.size_linear Braun.size.size_log_sq.

Require Import Braun.make_array.make_array_nlogn1.
Require Import Braun.make_array.make_array_nlogn1_fold.
Require Import Braun.make_array.make_array_nlogn2.

Require Import Braun.monad.monad.
Require Import Braun.sub1.sub1.

Require Import Braun.sort.isort.
Require Import Braun.sort.mergesort.

Require Import Braun.fib.fib.
Require Import Braun.clrs.zip.
Require Import Braun.clrs.rbt_search.
Require Import Braun.clrs.rbt_insert.

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
Extraction Inline projT1 projT2.

Extraction "extract.ml" insert_log.insert
           size_linear.size_linear
           size_log_sq.size

           copy_linear.copy_linear
           copy_fib_log.copy_fib
           copy_log_sq.copy_log_sq
           copy_log.copy

           make_array_nlogn1.make_array_naive
           make_array_nlogn1_fold.make_array_naive
           make_array_nlogn2.make_array_td
           sub1.sub1.sub1

           sort.isort.isort
           sort.mergesort.mergesort

           fib.fib.fib_rec
           fib.fib.fib_iter

           clrs.zip.minsert_at
           clrs.zip.minsertz_at
           clrs.rbt_search.bst_search
           clrs.rbt_insert.rbt_insert.
