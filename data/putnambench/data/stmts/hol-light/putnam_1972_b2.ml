(*
  Statement-only formalization of PutnamBench artifact putnam_1972_b2:
  the maximum elapsed time for a twice-differentiable real motion whose
  acceleration is nonincreasing, with prescribed displacement and endpoint
  velocities. This file contains no proof.
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
   let differentiable_at =
     \(g:real->real) (a:real).
       ?d. has_derivative_at g d a in
   let antitone_on =
     \(g:real->real) (u:real->bool).
       !a b. a IN u /\ b IN u /\ a <= b ==> g b <= g a in
   let solution =
     \(s:real) (v:real). &2 * s / v in
   let valid =
     \(s:real) (v:real) (t:real) (x:real->real).
       let interval = {w:real | &0 <= w /\ w <= t} in
       &0 < t /\
       (!w:real.
          w IN interval
          ==> differentiable_at x w /\
              differentiable_at (deriv x) w) /\
       antitone_on (deriv (deriv x)) interval /\
       deriv x (&0) = &0 /\
       deriv x t = v /\
       x t - x (&0) = s in
   !s v:real.
     &0 < s /\ &0 < v
     ==> (?x:real->real. valid s v (solution s v) x) /\
         (!t:real.
            t > solution s v
            ==> ~(?x:real->real. valid s v t x))`;;
