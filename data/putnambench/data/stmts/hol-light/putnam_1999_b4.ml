(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1999_b4:
  a positive real function with positive derivatives through order three and
  continuous third derivative, bounded above by the function itself, has
  first derivative everywhere less than twice the function. This file
  contains no proof.
*)

let statement =
  `let has_derivative =
     \(g:real->real) (l:real) (x:real).
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real.
                 &0 < abs (y - x) /\ abs (y - x) < d
                 ==> abs ((g y - g x) / (y - x) - l) < e in
   let continuous =
     \(g:real->real).
       !x e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !y:real.
                 abs (y - x) < d ==> abs (g y - g x) < e in
   !f:real->real.
     let f1 = \x:real. @l:real. has_derivative f l x in
     let f2 = \x:real. @l:real. has_derivative f1 l x in
     let f3 = \x:real. @l:real. has_derivative f2 l x in
     (!x:real. has_derivative f (f1 x) x) /\
     (!x:real. has_derivative f1 (f2 x) x) /\
     (!x:real. has_derivative f2 (f3 x) x) /\
     continuous f3 /\
     (!x:real.
        &0 < f x /\ &0 < f1 x /\ &0 < f2 x /\ &0 < f3 x) /\
     (!x:real. f3 x <= f x)
     ==> !x:real. f1 x < &2 * f x`;;
