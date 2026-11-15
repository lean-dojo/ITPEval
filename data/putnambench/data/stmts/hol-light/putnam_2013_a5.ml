(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a5:
  area-definiteness of coefficients for triangles in the Euclidean plane
  implies area-definiteness for triangles in three-dimensional Euclidean
  space. This file contains no proof.
*)

let statement =
  `let area2 =
     \(P:real^2) (Q:real^2) (R:real^2).
       abs ((Q$1 - P$1) * (R$2 - P$2) -
            (Q$2 - P$2) * (R$1 - P$1)) / &2 in
   let area3 =
     \(P:real^3) (Q:real^3) (R:real^3).
       sqrt
         (((Q$2 - P$2) * (R$3 - P$3) -
           (Q$3 - P$3) * (R$2 - P$2)) pow 2 +
          ((Q$3 - P$3) * (R$1 - P$1) -
           (Q$1 - P$1) * (R$3 - P$3)) pow 2 +
          ((Q$1 - P$1) * (R$2 - P$2) -
           (Q$2 - P$2) * (R$1 - P$1)) pow 2) / &2 in
   !m:num. !a:num->num->num->real.
     3 <= m /\
     (!A:num->real^2.
        &0 <=
        sum (0..m - 1)
          (\i:num.
             sum (i + 1..m - 1)
               (\j:num.
                  sum (j + 1..m - 1)
                    (\k:num. a i j k * area2 (A i) (A j) (A k)))))
     ==>
     !A:num->real^3.
       &0 <=
       sum (0..m - 1)
         (\i:num.
            sum (i + 1..m - 1)
              (\j:num.
                 sum (j + 1..m - 1)
                   (\k:num. a i j k * area3 (A i) (A j) (A k))))`;;
