(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2022_b5:
  the parameters for which every integer linear combination of independent
  {-1, 0, 1}-valued variables is most likely to equal zero are exactly the
  real interval [0, 1/4]. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pred_setTheory realTheory
     real_sigmaTheory;

val putnam_2022_b5 =
  ``!p : real.
    !Xset : num -> int list set.
    !Xprob : num -> int list -> real.
    !P : num -> int -> int list -> real.
      (!n : num.
         0 < n
         ==>
         Xset n =
           {X : int list |
              LENGTH X = n /\
              EVERY
                (\x : int. x = 1 \/ x = -1 \/ x = 0)
                X}) /\
      (!n : num. !X : int list.
         0 < n /\ LENGTH X = n
         ==>
         Xprob n X =
           REAL_PROD_IMAGE
             (\i : num.
                if EL i X = 1 \/ EL i X = -1
                then p
                else 1 - 2 * p)
             (count n)) /\
      (!n : num. !b : int. !a : int list.
         0 < n /\ LENGTH a = n
         ==>
         P n b a =
           REAL_SUM_IMAGE
             (Xprob n)
             {X : int list |
                X IN Xset n /\
                ITSET
                  (\i : num. \s : int. EL i a * EL i X + s)
                  (count n)
                  0 =
                b})
      ==>
      let putnam_2022_b5_solution =
        {q : real | 0 <= q /\ q <= 1 / 4}
      in
        ((0 <= p /\
          p <= 1 / 2 /\
          !n : num. !b : int. !a : int list.
            0 < n /\ LENGTH a = n
            ==>
            P n 0 a >= P n b a)
         <=>
         p IN putnam_2022_b5_solution)``;
