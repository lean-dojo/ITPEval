(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2025_a5
  (putnambench__hol4__putnam_2025_a5): the sign sequences maximizing the
  number of permutations with prescribed consecutive ascent and descent
  directions are exactly the two alternating sequences. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory;

val putnam_2025_a5 =
  ``let valid_signs =
      \n : num.
      \s : int list.
        LENGTH s = n /\
        EVERY (\x : int. x = 1 \/ x = ~1) s
    in
    let f =
      \n : num.
      \s : int list.
        CARD
          {p : num list |
             PERM p (GENLIST I (n + 1)) /\
             !i : num.
               i < n
               ==>
               0 <
                 EL i s *
                   (int_of_num (EL (SUC i) p) -
                    int_of_num (EL i p))}
    in
    let alternating =
      \n : num.
      \s : int list.
        (!i : num.
           i < n
           ==>
           EL i s = (~1 : int) ** (i + 1)) \/
        (!i : num.
           i < n
           ==>
           EL i s = (~1 : int) ** i)
    in
      !n : num. !s : int list.
        1 <= n /\ valid_signs n s
        ==>
        ((!t : int list.
            valid_signs n t
            ==>
            f n t <= f n s)
         <=>
         alternating n s)``;
