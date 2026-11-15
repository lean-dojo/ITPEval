(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2016_a1:
  the least positive derivative order for which every integer-coefficient
  polynomial has values divisible by 2016 at every integer is 8. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory;

val putnam_2016_a1 =
  ``let eval_int_poly =
      \coeffs : int list.
      \x : int.
        FOLDR (\c acc. c + x * acc) 0 coeffs;
      derivative =
        \coeffs : int list.
          GENLIST
            (\i. int_of_num (SUC i) * EL (SUC i) coeffs)
            (PRE (LENGTH coeffs));
      admissible =
        \j : num.
          0 < j /\
          !coeffs : int list. !k : int.
            (2016 : int) int_divides
              eval_int_poly (FUNPOW derivative j coeffs) k
    in
      admissible 8 /\
      !j : num. admissible j ==> 8 <= j``;
