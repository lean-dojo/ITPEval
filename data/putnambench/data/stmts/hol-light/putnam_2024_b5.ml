(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b5
  (putnambench__hol-light__putnam_2024_b5): the number of pairs of
  nondecreasing positive-integer sequences of prescribed positive lengths
  with a shared upper bound z at most n is a polynomial in positive n with
  nonnegative rational coefficients. This file contains no proof.
*)

needs "Library/floor.ml";;

let statement =
  `let qualifying =
     \(q:num) (w:num list) (z:num).
       LENGTH w = q /\
       (!i j:num.
          i < j /\ j < q
          ==> EL i w <= EL j w) /\
       1 <= EL 0 w /\
       EL (q - 1) w <= z in
   !k m:num. !f:num->num.
     0 < k /\
     0 < m /\
     (!n:num.
        f n =
        CARD
          {(x,y,z):num list#num list#num |
             qualifying k x z /\
             qualifying m y z /\
             z <= n})
     ==>
     ?d:num. ?a:num->real.
       (!i:num. rational (a i) /\ &0 <= a i) /\
       (!i:num. d < i ==> a i = &0) /\
       (!n:num.
          0 < n
          ==> &(f n) =
              sum (0..d) (\i:num. a i * (&n) pow i))`;;
