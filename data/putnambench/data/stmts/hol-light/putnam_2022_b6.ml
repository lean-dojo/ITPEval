(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b6
  (putnambench__hol-light__putnam_2022_b6): classification of continuous
  positive-real-valued functions on the positive reals satisfying the stated
  functional equation. This file contains no proof.
*)

let statement =
  `let continuous_on_positive =
     \(f:real->real).
       !x:real.
         &0 < x
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       &0 < y /\ abs (y - x) < d
                       ==> abs (f y - f x) < e in
   let satisfies_equation =
     \(f:real->real).
       !x y:real.
         &0 < x /\ &0 < y
         ==>
         f (x * f y) + f (y * f x) = &1 + f (x + y) in
   let is_solution =
     \(f:real->real).
       ?c:real.
         &0 <= c /\
         !x:real.
           &0 < x ==> f x = &1 / (&1 + c * x) in
   !f:real->real.
     (!x:real. &0 < x ==> &0 < f x) /\
     continuous_on_positive f
     ==>
     (satisfies_equation f <=> is_solution f)`;;
