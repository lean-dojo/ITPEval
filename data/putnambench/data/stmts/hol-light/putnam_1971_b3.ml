(*
  Statement-only formalization of PutnamBench artifact putnam_1971_b3:
  the real times at which one equal-speed traveler has completed exactly twice
  as many laps as a later-starting traveler have Lebesgue measure one. This
  file contains no proof.
*)

let statement =
  `let floor_real =
     \x:real. @z:real. integer z /\ z <= x /\ x < z + &1 in
   let cover_length =
     \(a:num->real) (b:num->real).
       sup (IMAGE
             (\n. sum (0..n) (\k. b k - a k))
             (:num)) in
   let lebesgue_outer_measure =
     \(s:real->bool).
       inf {m:real |
              ?a b:num->real.
                (!n. a n <= b n) /\
                (?B. !n. sum (0..n) (\k. b k - a k) <= B) /\
                (!x. x IN s ==> ?n. a n < x /\ x < b n) /\
                m = cover_length a b} in
   !tau:real.
     &0 < tau
     ==> lebesgue_outer_measure
           {t:real |
              tau <= t /\
              floor_real t = &2 * floor_real (t - tau)} = &1`;;
