(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2012_a3:
  uniqueness and closed form of a continuous real function on [-1,1]
  satisfying a functional equation, a normalization, and a finite left limit.
  This file contains no proof.
*)

let statement =
  `let interval =
     \x:real. -- &1 <= x /\ x <= &1 in
   let continuous_on_interval =
     \(f:real->real).
       !x:real.
         interval x
         ==> !e:real.
               &0 < e
               ==> ?d:real.
                     &0 < d /\
                     !y:real.
                       interval y /\ abs (y - x) < d
                       ==> abs (f y - f x) < e in
   let has_finite_left_limit =
     \(g:real->real).
       ?l:real.
         !e:real.
           &0 < e
           ==> ?d:real.
                 &0 < d /\
                 !x:real.
                   x < &1 /\ &1 - x < d
                   ==> abs (g x - l) < e in
   let satisfies =
     \(f:real->real).
       continuous_on_interval f /\
       (!x:real.
          interval x
          ==> f x =
              ((&2 - x pow 2) / &2) *
              f (x pow 2 / (&2 - x pow 2))) /\
       f (&0) = &1 /\
       has_finite_left_limit
         (\x:real. f x / sqrt (&1 - x)) in
   let solution =
     \x:real. sqrt (&1 - x pow 2) in
   satisfies solution /\
   !f:real->real.
     satisfies f
     ==> !x:real. interval x ==> f x = solution x`;;
