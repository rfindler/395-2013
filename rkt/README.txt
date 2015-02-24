To make the coq-to-coq fit into the Makefile and get it to generate
the right += expressions requires a few steps.

Create a racket file that contains an implementation of the function
in the monad, either using the parenthesized notation, like
rkt/diff.rkt, or the coq reader (which has less support), like
rkt/insert.rkt.

This is a standalone program that will run (even if the function
doesn't typecheck) and can be used to compute the running time as well
as the results. Eg:

  Welcome to Racket v6.1.1.8.
  > (require "diff.rkt" tmonad)
  > (diff (bt_node 1 bt_mt bt_mt) 1)
  0
  15

The first result is the result of the function and the second result
is the number of abstract steps. This can be useful to experiment with
the running time as a function of the input size when you're not sure
what the precise running time is.

The tmonad language also generates a main module which, when run,
prints out the coq code for the function with the right += expressions
inserted. Eg:

  % racket diff.rkt 
  (* this file was generated automatically from diff.rkt *)
  Program Fixpoint diff {A:Set} (b:@bin_tree A) (m:nat) {measure m}
  : {! res !:! nat !<! c !>!
       diff_result A b m res c !} :=
    match b, m with
      | bt_mt, _ => 
        += 4; 
        <== 0
      | bt_node x _ _, 0 => 
        += 4; 
        <== 1
      | bt_node x s t, S m' => 
        if (even_odd_dec m)
        then (o <- diff t (div2 (m' - 1));
              += 13; 
              <== o)
        else (o <- diff s (div2 m');
              += 11; 
              <== o)
    end.

This generated code has the free variable "diff_result" in but
otherwise it has the same things as in the Racket version (the
tmonad language includes things like even_odd_dec and div2 and
other things of that ilk to run the programs in Racket, but they just
turn into Coq identifiers in the generated code output).

To use it in coq, add the "racket diff.rkt" command-line to the
Makefile:

size/diff_gen.v: rkt/diff.rkt $(GEN_DEPS)
	racket rkt/diff.rkt > size/diff_gen.v

using GEN_DEPS as a dependency as well as the racket input file.

Also, add a dependency to the tmonad-gen line in the Makefile, in this
case, since the results are then put into size/diff_gen.v, add
size/diff_gen.v to the tmonad-gen dependency list.

Then, in the Coq file where you will use this function,
size/size_log_sq.v in this case, add:

  Load "diff_gen.v"

but be sure that you've defined diff_result first.

Once that is all set up the coq-side automatic makefile generation
should work, picking up the dependency on the "Load"ed file.
