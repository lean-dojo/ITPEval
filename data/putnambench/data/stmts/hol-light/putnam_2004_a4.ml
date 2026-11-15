(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2004_a4:
  the identity expressing a product of real variables as a rational linear
  combination of nth powers of {-1,0,1}-coefficient linear forms. This file
  contains no proof.
*)

let statement =
  `let is_rational =
     \x:real.
       ?p q:int.
         ~(q = &0) /\
         x = real_of_int p / real_of_int q in
   !n:num.
     0 < n
     ==> ?N:num. ?c:num->real. ?a:num->num->real.
           (!i:num. i < N ==> is_rational (c i)) /\
           (!i j:num.
              i < N /\ j < n
              ==> a i j = -- &1 \/ a i j = &0 \/ a i j = &1) /\
           !x:num->real.
             product (0..n-1) x =
             sum {i:num | i < N}
               (\i:num.
                  c i *
                  (sum (0..n-1) (\j:num. a i j * x j)) pow n)`;;
