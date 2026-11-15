(*
  Statement-only formalization of PutnamBench artifact putnam_1970_b4:
  a twice-differentiable real function with prescribed displacement, zero
  endpoint derivatives, and bounded first derivative has a large second
  derivative somewhere on the unit interval. This file contains no proof.
*)

let statement =
  `let has_derivative_at =
     \(g:real->real) (d:real) (a:real).
       !e. &0 < e
           ==> ?delta. &0 < delta /\
                       !y. &0 < abs (y - a) /\ abs (y - a) < delta
                           ==> abs ((g y - g a) / (y - a) - d) < e in
   let deriv =
     \(g:real->real) (a:real). @d. has_derivative_at g d a in
   !x:real->real.
     (!a. &0 <= a /\ a <= &1 ==> ?d. has_derivative_at x d a) /\
     (!a. &0 <= a /\ a <= &1
          ==> ?d. has_derivative_at (deriv x) d a) /\
     x (&1) - x (&0) = &1 /\
     deriv x (&0) = &0 /\
     deriv x (&1) = &0 /\
     (!t. &0 < t /\ t < &1 ==> abs (deriv x t) <= &3 / &2)
     ==> ?t.
           &0 <= t /\ t <= &1 /\
           abs (deriv (deriv x) t) >= &9 / &2`;;
