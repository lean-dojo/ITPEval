(*
  Statement-only formalization of PutnamBench artifact putnam_1980_b5:
  characterization of the nonnegative parameters for which a class of
  nonnegative strictly increasing convex continuous functions on [0,1] is
  closed under pointwise multiplication. This file contains no proof.
*)

let statement =
  `let in_unit_interval =
     \x:real. &0 <= x /\ x <= &1 in
   let in_S =
     \t (f:real->real).
       (!x. in_unit_interval x ==> &0 <= f x) /\
       (!x y.
          in_unit_interval x /\ in_unit_interval y /\ x < y
          ==> f x < f y) /\
       (!u v s.
          in_unit_interval u /\
          in_unit_interval v /\
          in_unit_interval s
          ==> f (s * u + (&1 - s) * v)
              <= s * f u + (&1 - s) * f v) /\
       (!x.
          in_unit_interval x
          ==> !e. &0 < e
                  ==> ?d. &0 < d /\
                          !y.
                            in_unit_interval y /\ abs (y - x) < d
                            ==> abs (f y - f x) < e) /\
       t * (f (&2 / &3) - &2 * f (&1 / &3) + f (&0))
       <= f (&1) - &2 * f (&2 / &3) + f (&1 / &3) in
   let putnam_1980_b5_solution =
     \t:real. t <= &1 in
   !t:real.
     &0 <= t
     ==>
     ((!f g:real->real.
         in_S t f /\ in_S t g
         ==> in_S t (\x. f x * g x)) <=>
      putnam_1980_b5_solution t)`;;
