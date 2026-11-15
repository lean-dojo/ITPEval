(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_b5:
  integer square matrices whose every nonempty principal minor has odd
  determinant remain very odd under every positive matrix power. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory permutesTheory;

val putnam_2021_b5 =
  ``let determinant =
      \(s : num -> bool) (A : num -> num -> int).
        ITSET
          (\p acc.
             (if evenperm p then
                ITSET (\i q. A i (p i) * q) s 1
              else
                -(ITSET (\i q. A i (p i) * q) s 1)) +
             acc)
          {p : num -> num | p permutes s}
          0
    in
    let matrix_mul =
      \n : num. \A B : num -> num -> int. \i j : num.
        ITSET
          (\r : num. \sum : int. A i r * B r j + sum)
          (count n)
          0
    in
    let matrix_one =
      \i j : num. if i = j then (1 : int) else 0
    in
    let matrix_pow =
      \n : num. \A : num -> num -> int. \k : num.
        FUNPOW (\B. matrix_mul n B A) k matrix_one
    in
    let very_odd =
      \n : num. \A : num -> num -> int.
        !s : num -> bool.
          s SUBSET count n /\ s <> {}
          ==>
          ?q : int. determinant s A = 2 * q + 1
    in
      !n : num.
        1 <= n
        ==>
        !A : num -> num -> int.
          very_odd n A
          ==>
          !k : num.
            1 <= k
            ==>
            very_odd n (matrix_pow n A k)``;
