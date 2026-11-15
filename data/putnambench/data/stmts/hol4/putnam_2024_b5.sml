(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b5
  (putnambench__hol4__putnam_2024_b5): f(n) counts triples (x,y,z), where x
  and y are nondecreasing positive-integer sequences of prescribed positive
  lengths and z is a chosen common upper bound with z <= n; this count is a
  polynomial in n with nonnegative rational coefficients. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory ratTheory;

val putnam_2024_b5 =
  ``let qualifying =
      \q : num. \w : num list. \z : num.
        LENGTH w = q /\
        (!i j : num.
           i < j /\ j < q
           ==>
           EL i w <= EL j w) /\
        1 <= EL 0 w /\
        EL (q - 1) w <= z
    in
      !k m : num. !f : num -> num.
        0 < k /\
        0 < m /\
        (!n : num.
           f n =
           CARD
             {t : num list # num list # num |
                qualifying k (FST t) (SND (SND t)) /\
                qualifying m (FST (SND t)) (SND (SND t)) /\
                SND (SND t) <= n})
        ==>
        ?d : num. ?P : num -> rat.
          (!i : num. d < i ==> P i = 0q) /\
          (!i : num. 0q <= P i) /\
          (!n : num.
             0 < n
             ==>
             rat_of_num (f n) =
             ITSET
               (\i : num. \acc : rat.
                  P i * rat_expn (rat_of_num n) i + acc)
               (count (d + 1))
               0q)``;
