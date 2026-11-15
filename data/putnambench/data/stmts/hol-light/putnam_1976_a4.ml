(*
  Statement-only formalization of PutnamBench artifact putnam_1976_a4:
  another real root of the specified irreducible integer cubic is one of two
  explicit rational functions of the given root. This file contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = &0) /\
         x = real_of_int p / real_of_int q in
   let P =
     \a b x:real.
       x pow 3 + a * x pow 2 + b * x - &1 in
   let Q =
     \c d x:real.
       x pow 3 + c * x pow 2 + d * x + &1 in
   !a b c d:int. !r:real.
     P (real_of_int a) (real_of_int b) r = &0 /\
     (!x:real.
        is_rational x
        ==> ~(P (real_of_int a) (real_of_int b) x = &0)) /\
     Q (real_of_int c) (real_of_int d) (r + &1) = &0
     ==>
     ?s:real.
       P (real_of_int a) (real_of_int b) s = &0 /\
       (s = --(&1 / (r + &1)) \/ s = --(r + &1) / r)`;;
