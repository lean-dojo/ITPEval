(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b4
  (putnambench__hol-light__putnam_2022_b4): classification of cyclic sequences
  of distinct real numbers whose consecutive triples form three-term
  arithmetic progressions when sorted. This file contains no proof.
*)

let statement =
  `let ap3 =
     \x0 x1 x2:real.
       !o0 o1 o2:real.
         o0 < o1 /\
         o1 < o2 /\
         {o0,o1,o2} = {x0,x1,x2}
         ==> o1 - o0 = o2 - o1 in
   let cyclic_progression =
     \n (x:num->real).
       (!i j:num.
          i < n /\ j < n /\ ~(i = j)
          ==> ~(x i = x j)) /\
       (!i:num.
          i < n
          ==> ap3
                (x i)
                (x ((i + 1) MOD n))
                (x ((i + 2) MOD n))) in
   !n:num.
     (4 <= n /\ ?x:num->real. cyclic_progression n x)
     <=>
     9 <= n /\ 3 divides n`;;
