(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a4:
  the sum of squared distances between any n points on the unit sphere in
  Euclidean three-space is at most n squared. This file contains no proof.
*)

let statement =
  `let unit3 =
     \(p:real#(real#real)).
       (FST p) pow 2 +
       (FST (SND p)) pow 2 +
       (SND (SND p)) pow 2 = &1 in
   let sqdist3 =
     \(p:real#(real#real)) (q:real#(real#real)).
       (FST p - FST q) pow 2 +
       (FST (SND p) - FST (SND q)) pow 2 +
       (SND (SND p) - SND (SND q)) pow 2 in
   !n:num. !S:num->real#(real#real).
     (!i:num. i < n ==> unit3 (S i))
     ==> sum {i:num | i < n}
             (\i. sum {j:num | j < n}
                      (\j. if i < j
                           then sqdist3 (S i) (S j)
                           else &0))
         <= &(n EXP 2)`;;
