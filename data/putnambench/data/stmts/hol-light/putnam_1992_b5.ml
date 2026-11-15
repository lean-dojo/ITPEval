(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1992_b5:
  boundedness of the rational sequence of factorial-normalized determinants
  with diagonal entries 3 through n+1 and all off-diagonal entries 1. This
  file contains no proof.
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
   let D =
     \n:num.
       ndet
         (\i j:num. if i = j then &(i + 3) else &1)
         (n - 1) in
   let putnam_1992_b5_solution = F in
   ((?r:real.
       !n:num.
         2 <= n
         ==> abs (D n / &(FACT n)) <= r)
    <=> putnam_1992_b5_solution)`;;
