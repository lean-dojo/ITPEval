(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1994_a4:
  integer-entry 2 by 2 matrices whose first five affine combinations are
  invertible over the integers have an invertible sixth combination. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory fcpTheory;

val putnam_1994_a4 =
  ``let matrix_add =
      \A B : int['N]['N].
        ((FCP i j. A ' i ' j + B ' i ' j) : int['N]['N])
    in
    let matrix_scale =
      \k : int. \A : int['N]['N].
        ((FCP i j. k * A ' i ' j) : int['N]['N])
    in
    let matrix_mul =
      \A B : int['N]['N].
        ((FCP i j.
            A ' i ' 0 * B ' 0 ' j + A ' i ' 1 * B ' 1 ' j) :
          int['N]['N])
    in
    let matrix_one =
      ((FCP i j. if i = j then 1 else 0) : int['N]['N])
    in
    let matrix_invertible =
      \A : int['N]['N].
        ?C : int['N]['N].
          matrix_mul A C = matrix_one /\
          matrix_mul C A = matrix_one
    in
      !A B : int['N]['N].
        dimindex (:'N) = 2 /\
        matrix_invertible A /\
        matrix_invertible (matrix_add A B) /\
        matrix_invertible (matrix_add A (matrix_scale 2 B)) /\
        matrix_invertible (matrix_add A (matrix_scale 3 B)) /\
        matrix_invertible (matrix_add A (matrix_scale 4 B))
        ==>
        matrix_invertible (matrix_add A (matrix_scale 5 B))``;
