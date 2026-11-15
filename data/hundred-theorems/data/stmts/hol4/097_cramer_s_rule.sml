(*
  Statement-only formalization of "Cramer's Rule" from Hundred Theorems
  artifact hundred-theorems__hol4__097. For a square real matrix on an
  arbitrary finite index set with nonzero determinant, Ax = b holds exactly
  when each coordinate of x is the determinant obtained by replacing the
  corresponding column with b, divided by the determinant of A. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory permutesTheory realTheory;

val cramer_s_rule =
  ``let determinant =
      \(s : 'i -> bool) (A : 'i -> 'i -> real).
        ITSET
          (\p acc.
            (if evenperm p then
               ITSET (\i q. A i (p i) * q) s 1
             else
               -(ITSET (\i q. A i (p i) * q) s 1)) + acc)
          {p : 'i -> 'i | p permutes s} 0
    in
    let replace_column =
      \(A : 'i -> 'i -> real) (b : 'i -> real) (k : 'i)
       (i : 'i) (j : 'i).
        if j = k then b i else A i j
    in
    let matrix_vec_mul =
      \(s : 'i -> bool) (A : 'i -> 'i -> real) (x : 'i -> real)
       (i : 'i).
        ITSET (\j acc. A i j * x j + acc) s 0
    in
      !(s : 'i -> bool) (A : 'i -> 'i -> real)
       (x : 'i -> real) (b : 'i -> real).
        FINITE s /\ determinant s A <> 0
        ==>
        ((!i. i IN s ==> matrix_vec_mul s A x i = b i) <=>
         (!k. k IN s ==>
              x k = determinant s (replace_column A b k) / determinant s A))``;
