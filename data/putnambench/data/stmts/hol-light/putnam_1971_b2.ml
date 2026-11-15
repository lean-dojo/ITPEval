(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b2:
  classification of real functions satisfying a functional equation away
  from 0 and 1. This file contains no proof.
*)

let statement =
  `let S = {x:real | ~(x = &0) /\ ~(x = &1)} in
   let satisfies =
     \(f:real->real).
       !x. x IN S ==> f x + f ((x - &1) / x) = &1 + x in
   let is_solution =
     \(f:real->real).
       f = (\x:real.
              (x pow 3 - x pow 2 - &1) / (&2 * x * (x - &1))) in
   (!f:real->real. is_solution f ==> satisfies f) /\
   (!f:real->real.
      satisfies f
      ==> ?g:real->real.
            is_solution g /\ !x. x IN S ==> f x = g x)`;;
