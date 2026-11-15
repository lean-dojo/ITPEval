(*
  Statement-only formalization of PutnamBench artifact putnam_1972_a6:
  a normalized highest moment and vanishing lower moments force an integrable
  real function on [0,1] to exceed a specified level on a set of positive
  Lebesgue measure. This file contains no proof.
*)

let statement =
  `let interval01 = {x:real | &0 <= x /\ x <= &1} in
   let cover_bound =
     \(s:real->bool) (B:real).
       &0 <= B /\
       ?a b:num->real.
         (!k. a k <= b k) /\
         (!x. x IN s ==> ?k. a k < x /\ x < b k) /\
         (!N. sum (0..N) (\k. b k - a k) <= B) in
   let outer_measure =
     \(s:real->bool). inf {B:real | cover_bound s B} in
   let measurable01 =
     \(s:real->bool).
       s SUBSET interval01 /\
       outer_measure s + outer_measure (interval01 DIFF s) = &1 in
   let nonnegative_simple =
     \(h:real->real).
       FINITE (IMAGE h interval01) /\
       (!x. x IN interval01 ==> &0 <= h x) /\
       (!c. c IN IMAGE h interval01
            ==> measurable01 {x | x IN interval01 /\ h x = c}) in
   let simple_integral =
     \(h:real->real).
       sum (IMAGE h interval01)
         (\c. c * outer_measure {x | x IN interval01 /\ h x = c}) in
   let lower_integrals =
     \(g:real->real).
       {z:real |
          ?h:real->real.
            nonnegative_simple h /\
            (!x. x IN interval01 ==> h x <= g x) /\
            z = simple_integral h} in
   let finite_nonnegative_integral =
     \(g:real->real).
       ?B:real. !z. z IN lower_integrals g ==> z <= B in
   let nonnegative_integral =
     \(g:real->real). sup (lower_integrals g) in
   let positive_part =
     \(g:real->real) x. if &0 <= g x then g x else &0 in
   let negative_part =
     \(g:real->real) x. if g x <= &0 then --(g x) else &0 in
   let measurable_function =
     \(g:real->real).
       !a:real. measurable01 {x | x IN interval01 /\ g x < a} in
   let lebesgue_integrable =
     \(g:real->real).
       measurable_function g /\
       finite_nonnegative_integral (positive_part g) /\
       finite_nonnegative_integral (negative_part g) in
   let lebesgue_integral =
     \(g:real->real).
       nonnegative_integral (positive_part g) -
       nonnegative_integral (negative_part g) in
   !f:real->real n:num.
     lebesgue_integrable f /\
     (!i:num.
        i < n
        ==> lebesgue_integral (\x. x pow i * f x) = &0) /\
     lebesgue_integral (\x. x pow n * f x) = &1
     ==> ?s:real->bool.
           s SUBSET interval01 /\
           measurable01 s /\
           &0 < outer_measure s /\
           (!x. x IN s
                ==> (&2:real) pow n * &(n + 1) <= abs(f x))`;;
