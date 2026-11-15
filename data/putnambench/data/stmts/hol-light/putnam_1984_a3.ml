(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1984_a3:
  the punctured limit at a of a normalized determinant of a parity-patterned
  2n by 2n real matrix. This file contains no proof.
*)

let statement =
  `let ndet =
     \(A:num->num->real) n.
       sum {p:num->num |
              BIJ p (0..n-1) (0..n-1) /\
              (!i:num. ~(i IN 0..n-1) ==> p i = i)}
           (\p.
              (if EVEN
                    (CARD
                      {(i,j) |
                         i < n /\ j < n /\ i < j /\ p j < p i})
               then &1
               else -- &1) *
              product (0..n-1) (\i. A i (p i))) in
   let tends_at_punctured =
     \(f:real->real) a l.
       !e:real.
         &0 < e
         ==> ?d:real.
               &0 < d /\
               !x:real.
                 &0 < abs (x - a) /\ abs (x - a) < d
                 ==> abs (f x - l) < e in
   !n:num. !a b:real.
     0 < n /\ ~(a = b)
     ==> tends_at_punctured
           (\x:real.
              ndet
                (\i j:num.
                   if i = j then x
                   else if EVEN (i + j) then a
                   else b)
                (2 * n) /
              ((x - a) pow (2 * n - 2)))
           a
           ((&n pow 2) * (a pow 2 - b pow 2))`;;
