(*
  Statement-only formalization of PutnamBench artifact putnam_1975_a5:
  positive linearly independent solutions of a second-order differential
  equation yield a scaled square-root product satisfying the associated
  nonlinear differential equation on a real interval. This file contains no
  proof.
*)

let statement =
  `let continuous =
     \g:real->real.
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 abs (y - x) < delta ==> abs (g y - g x) < e in
   let has_derivative_at =
     \(g:real->real) (d:real) (x:real).
       !e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < delta
                 ==> abs ((g y - g x) / (y - x) - d) < e in
   let deriv =
     \(g:real->real) (x:real). @d:real. has_derivative_at g d x in
   let contdiff2 =
     \g:real->real.
       (!x:real. ?d:real. has_derivative_at g d x) /\
       (!x:real. ?d:real. has_derivative_at (deriv g) d x) /\
       continuous (deriv g) /\
       continuous (deriv (deriv g)) in
   let real_interval =
     \s:real->bool.
       !a b x:real.
         a IN s /\ b IN s /\ a <= x /\ x <= b ==> x IN s in
   !i:real->bool. !f y1 y2:real->real.
     real_interval i /\
     continuous f /\
     contdiff2 y1 /\
     contdiff2 y2 /\
     (!x:real.
        deriv (deriv y1) x = f x * y1 x) /\
     (!x:real.
        deriv (deriv y2) x = f x * y2 x) /\
     (!c1 c2:real.
        (!x:real. c1 * y1 x + c2 * y2 x = &0)
        ==> c1 = &0 /\ c2 = &0) /\
     (!x:real. x IN i ==> &0 < y1 x /\ &0 < y2 x)
     ==> ?c:real.
           &0 < c /\
           let z = \x:real. c * sqrt (y1 x * y2 x) in
           !x:real.
             x IN i
             ==> deriv (deriv z) x +
                 &1 / (z x) pow 3 = f x * z x`;;
