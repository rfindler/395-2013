Require Import Arith.Div2 Arith.Even.

Require Import Braun.insert.insert_log.

Require Import Braun.copy.copy_linear Braun.copy.copy_fib_log.
Require Import Braun.copy.copy_log_sq Braun.copy.copy_log.

Require Import Braun.size.size_linear Braun.size.size_log_sq.

Require Import Braun.make_array.make_array_nlogn1.
Require Import Braun.make_array.make_array_nlogn1_fold.
Require Import Braun.make_array.make_array_nlogn2.
Require Import Braun.to_list.to_list_naive.

Require Import Braun.monad.monad.

Require Import Braun.arith.sub1.

Require Import Braun.sort.isort.
Require Import Braun.sort.mergesort.

Require Import Braun.fib.fib.
Require Import Braun.zippers.zip.
Require Import Braun.rbtrees.rbt_search.
Require Import Braun.rbtrees.rbt_insert.

Extract Inductive bool => "bool" [ "false" "true" ].
Extract Inductive sumbool => "bool" [ "false" "true" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inductive nat => 
"big_int" [ "zero_big_int" "succ_big_int" ]
      "(fun fO fS n -> if (eq_big_int n zero_big_int) then fO () else fS (pred_big_int n))".

Extract Constant plus => "add_big_int".
Extract Constant mult => "mult_big_int".
Extract Constant minus => "sub_big_int".

Extract Constant div2 => "fun a -> div_big_int a (big_int_of_int 2)".
Extract Constant even_odd_dec => "fun a -> not (eq_big_int zero_big_int (mod_big_int a (big_int_of_int 2)))".

Extract Inductive sigT => "(*)" [ "(,)" ].

Extraction Inline ret bind inc.
Extraction Inline projT1 projT2.

Extraction "post_extract.ml" insert_log.insert
           size_linear.size_linear
           size_log_sq.size

           copy_linear.copy_linear
           copy_fib_log.copy_fib
           copy_log_sq.copy_log_sq
           copy_log.copy

           make_array_nlogn1.make_array_naive
           make_array_nlogn1_fold.make_array_naive
           make_array_nlogn2.make_array_td
           to_list_naive.to_list_naive
           
           arith.sub1.sub1

           sort.isort.isort
           sort.mergesort.mergesort

           fib.fib.fib_rec
           fib.fib.fib_iter

           zippers.zip.minsert_at
           zippers.zip.minsertz_at
           rbtrees.rbt_search.bst_search
           rbtrees.rbt_insert.rbt_insert.
