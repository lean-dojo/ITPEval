(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b4:
  the determinant of the complex tournament matrix T + iW is a nonnegative
  integer divisible by 2^2010. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory permutesTheory realTheory
     complexTheory;

val putnam_2011_b4 =
  ``let determinant =
      \size : num. \M : num -> num -> complex.
        ITSET
          (\p : num -> num. \sum : complex.
             (if evenperm p then
                ITSET
                  (\row : num. \acc : complex. M row (p row) * acc)
                  (count size)
                  (1 : complex)
              else
                -(ITSET
                    (\row : num. \acc : complex. M row (p row) * acc)
                    (count size)
                    (1 : complex))) +
             sum)
          {p : num -> num | p permutes count size}
          (0 : complex)
    in
      !games : num -> num -> bool.
        let T =
          \row col : num.
            complex_of_real
              (&(CARD
                   {game : num |
                      game < 2011 /\
                      games game row = games game col}))
        in
        let W =
          \row col : num.
            complex_of_real
              (&(CARD
                   {game : num |
                      game < 2011 /\
                      games game row /\
                      ~games game col}) -
               &(CARD
                   {game : num |
                      game < 2011 /\
                      ~games game row /\
                      games game col}))
        in
          ?n : num.
            determinant 2011
              (\row col. T row col + i * W row col) =
              complex_of_real (&n) /\
            divides (2 EXP 2010) n``;
