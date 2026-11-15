(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a4
  (putnambench__hol-light__putnam_2025_a4): the least dimension of real square
  matrices whose commuting graph is the 2025-cycle. This file contains no
  proof.
*)

let statement =
  `let matrix_mul =
     \(k:num) (A:num->num->real) (B:num->num->real).
       \r c:num. sum {p:num | p < k} (\p. A r p * B p c) in
   let matrix_equal =
     \(k:num) (A:num->num->real) (B:num->num->real).
       !r c:num. r < k /\ c < k ==> A r c = B r c in
   let admissible =
     \k:num.
       ?A:num->num->num->real.
         !i j:num.
           i < 2025 /\ j < 2025 /\ i <= j
           ==>
           (matrix_equal k
              (matrix_mul k (A i) (A j))
              (matrix_mul k (A j) (A i)) <=>
            j - i = 0 \/ j - i = 1 \/ j - i = 2024) in
   admissible 3 /\
   (!k:num. admissible k ==> 3 <= k)`;;
