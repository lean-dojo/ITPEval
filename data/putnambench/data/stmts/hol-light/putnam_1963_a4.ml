(*
  Statement-only formalization of PutnamBench artifact putnam_1963_a4:
  the sharp lower bound 1 for the limsup of a ratio expression associated
  with every positive real sequence. This file contains no proof.
*)

let statement =
  `let term =
     \(a:num->real) (n:num).
       &n * ((&1 + a (n + 1)) / a n - &1) in
   let limsup_at_least =
     \(u:num->real) (c:real).
       !b. b < c ==> !N. ?n. N <= n /\ b < u n in
   (!a:num->real.
      (!n. &0 < a n)
      ==> limsup_at_least (term a) (&1)) /\
   (!c:real.
      &1 < c
      ==> ?a:num->real.
            (!n. &0 < a n) /\
            ~limsup_at_least (term a) c)`;;
