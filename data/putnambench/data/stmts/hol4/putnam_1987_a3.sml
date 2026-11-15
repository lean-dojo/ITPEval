(*
  Statement-only formalization of PutnamBench artifact putnam_1987_a3:
  the paired truth-value classification of positivity and monotonicity
  implications for solutions of y'' - 2 y' + y = 2 exp x. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory limTheory transcTheory;

(*
  diffn and higher_differentiable are constants from limTheory. In
  particular, diffn is the iterated derivative selected from diffl, and
  higher_differentiable requires the corresponding derivative to exist at
  every order through the requested one.
*)

val putnam_1987_a3 =
  ``(((!f : real -> real.
         (!x : real.
            higher_differentiable 1 f x /\
            higher_differentiable 2 f x /\
            diffn 2 f x - 2 * diffn 1 f x + f x = 2 * exp x /\
            0 < f x)
         ==>
         !x : real. 0 < diffn 1 f x)
      <=> F) /\
     ((!g : real -> real.
         (!x : real.
            higher_differentiable 1 g x /\
            higher_differentiable 2 g x /\
            diffn 2 g x - 2 * diffn 1 g x + g x = 2 * exp x /\
            0 < diffn 1 g x)
         ==>
         !x : real. 0 < g x)
      <=> T))``;

(* Reject accidental parser free variables in this closed statement. *)
val _ =
  if null (free_vars putnam_1987_a3) then ()
  else raise Fail "putnam_1987_a3 contains an unresolved free variable";
