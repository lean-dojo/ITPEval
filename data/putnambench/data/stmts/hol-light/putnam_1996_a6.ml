(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1996_a6:
  the classification, depending on a positive real parameter, of continuous
  real functions satisfying f(x) = f(x^2 + c). This file contains no proof.
*)

let statement =
  `let continuous_everywhere =
     \(f:real->real).
       !x e:real.
         &0 < e
         ==> ?delta:real.
               &0 < delta /\
               !y:real.
                 abs (y - x) < delta
                 ==> abs (f y - f x) < e in
   let continuous_on_interval =
     \(f:real->real) (c:real).
       !x:real.
         &0 <= x /\ x <= c
         ==> !e:real.
               &0 < e
               ==> ?delta:real.
                     &0 < delta /\
                     !y:real.
                       &0 <= y /\ y <= c /\
                       abs (y - x) < delta
                       ==> abs (f y - f x) < e in
   !c:real. !f:real->real.
     &0 < c
     ==>
     ((continuous_everywhere f /\
       (!x:real. f x = f (x pow 2 + c)))
      <=>
      (if c <= &1 / &4
       then ?d:real. !x:real. f x = d
       else
         continuous_on_interval f c /\
         f (&0) = f c /\
         (!x:real. &0 < x ==> f x = f (x pow 2 + c)) /\
         (!x:real. x < &0 ==> f x = f (--x))))`;;
