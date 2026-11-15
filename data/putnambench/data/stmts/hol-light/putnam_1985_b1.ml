(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b1:
  the five distinct integers -2, -1, 0, 1, 2 minimize the number of nonzero
  coefficients in their associated product of five monic linear factors.
  This file contains no proof.
*)

let statement =
  `let pmul =
     \p q:num->real. \k:num.
       sum (0..k) (\i:num. p i * q (k - i)) in
   let linear =
     \m:int. \k:num.
       if k = 0 then --(real_of_int m)
       else if k = 1 then &1
       else &0 in
   let p =
     \m1 m2 m3 m4 m5:int.
       pmul
         (pmul
           (pmul
             (pmul (linear m1) (linear m2))
             (linear m3))
           (linear m4))
         (linear m5) in
   let numnzcoeff =
     \q:num->real. CARD {k:num | ~(q k = &0)} in
   {--(&2:int), --(&1:int), (&0:int), (&1:int), (&2:int)} HAS_SIZE 5 /\
   (!a b c d e:int.
      {a,b,c,d,e} HAS_SIZE 5
      ==> numnzcoeff
            (p (--(&2:int)) (--(&1:int)) (&0:int) (&1:int) (&2:int))
          <= numnzcoeff (p a b c d e))`;;
