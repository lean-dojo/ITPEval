(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_b6
  (putnambench__hol-light__putnam_2023_b6): the determinant of the matrix
  counting nonnegative solutions to a*i + b*j = n. This file contains no
  proof.
*)

let statement =
  `let integer_det =
     \(A:num->num->int) n.
       isum {p:num->num |
               BIJ p (1..n) (1..n) /\
               (!i:num. ~(i IN 1..n) ==> p i = i)}
            (\p.
               (if EVEN
                     (CARD
                       {(i,j) |
                          i IN 1..n /\
                          j IN 1..n /\
                          i < j /\
                          p j < p i})
                then (&1:int)
                else --(&1:int)) *
               iproduct (1..n) (\i. A i (p i))) in
   let putnam_2023_b6_solution =
     \n:num.
       let k = (n + 1) DIV 2 in
       (if EVEN (k + 1) then (&1:int) else --(&1:int)) *
       (&2:int) * &k in
   !n:num. !S:num->num->int.
     0 < n /\
     (!i j:num.
        i IN 1..n /\
        j IN 1..n
        ==> S i j =
            &(CARD {(a,b) | a * i + b * j = n}))
     ==> integer_det S n = putnam_2023_b6_solution n`;;
