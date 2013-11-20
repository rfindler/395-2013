Require Import Arith List.
Require Import Arith.Even Arith.Div2.
Require Import CpdtTactics.

(* http://coq.inria.fr/library/Coq.Arith.Div2.html *)

Program Fixpoint break_it_up (n : nat) : nat :=
  if even_odd_dec n 
  then even_2n n _
  else odd_S2n n _.

Example b8 : break_it_up 8 = 4. compute. reflexivity. Qed.
Example b9 : break_it_up 9 = 4. compute. reflexivity. Qed.

Program Definition to_binary : nat -> (list bool) :=
  Fix lt_wf
      (fun x => list bool)
      (fun n to_binary => 
         match n with 
           | 0 => nil
           | S n' =>
             match even_odd_dec n with
               | left L => 
                 cons false (to_binary (proj1_sig (even_2n n L)) _)
               | right R => 
                 cons true (to_binary (proj1_sig (odd_S2n n R)) _)
             end
      end).
Obligation 1. apply lt_div2. crush. Qed.
Obligation 2. apply lt_div2. crush. Qed.

Example tb_1 : to_binary 1 = true :: nil.
  compute. reflexivity. Qed.
Example tb_2 : to_binary 2 = false :: true :: nil.
  compute. reflexivity. Qed.
Example tb_3 : to_binary 3 = true :: true :: nil.
  compute. reflexivity. Qed.
Example tb_11 : to_binary 11 = true :: true :: false :: true :: nil.
  compute. reflexivity. Qed.
