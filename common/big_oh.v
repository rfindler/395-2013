Set Implicit Arguments.

(* definition taken from Wikipedia *)
Definition big_oh f g := 
  exists n0 m, 
    forall n, 
      n0 < n -> 
      f(n) <= m * g(n).
