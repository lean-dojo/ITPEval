(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1990_a5:
  the universal assertion that ABAB = 0 implies BABA = 0 for same-size real
  square matrices is false. This file contains no proof.
*)

let statement =
  `let matrix_mul =
     \n:num. \(A:num->num->real) (B:num->num->real).
       \i j:num. sum (0..n - 1) (\k. A i k * B k j) in
   let is_zero =
     \n:num. \(A:num->num->real).
       !i j:num. i < n /\ j < n ==> A i j = &0 in
   let putnam_1990_a5_solution = F in
   ((!n:num.
       1 <= n
       ==> !A B:num->num->real.
             is_zero n
               (matrix_mul n (matrix_mul n (matrix_mul n A B) A) B)
             ==> is_zero n
                   (matrix_mul n (matrix_mul n (matrix_mul n B A) B) A))
    <=> putnam_1990_a5_solution)`;;
