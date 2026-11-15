(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a2
  (putnambench__hol-light__putnam_2025_a2): the sharp lower and upper
  coefficients bounding sin x by multiples of x(pi - x) on [0, pi]. This file
  contains no proof.
*)

needs "Library/transc.ml";;

let statement =
  `let lower_admissible =
     \a:real.
       !x:real.
         &0 <= x /\ x <= pi
         ==> a * x * (pi - x) <= sin x in
   let upper_admissible =
     \b:real.
       !x:real.
         &0 <= x /\ x <= pi
         ==> sin x <= b * x * (pi - x) in
   let is_greatest =
     \(s:real->bool) (a:real).
       s a /\ (!a':real. s a' ==> a' <= a) in
   let is_least =
     \(s:real->bool) (b:real).
       s b /\ (!b':real. s b' ==> b <= b') in
   let putnam_2025_a2_solution =
     (&1 / pi,&4 / pi pow 2) in
   !a b:real.
     ((a,b) = putnam_2025_a2_solution <=>
      is_greatest lower_admissible a /\
      is_least upper_admissible b)`;;
