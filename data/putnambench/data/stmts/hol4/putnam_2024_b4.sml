(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_b4
  (putnambench__hol4__putnam_2024_b4): the normalized expected position of the
  independent uniform integer-driven walk converges to (1 - exp(-2))/2.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory integerTheory realTheory;
open real_topologyTheory limTheory transcTheory;
open extrealTheory measureTheory probabilityTheory;

val putnam_2024_b4 =
  ``let integer_interval =
      \n : num.
        {z : int | 1 <= z /\ z <= int_of_num n}
    in
      !(p : 'omega p_space)
       (m a : num -> num -> 'omega -> int).
        prob_space p /\
        p_space p = UNIV /\
        (!n k : num.
           0 < n
           ==>
           random_variable (m n k) p (UNIV, POW UNIV) /\
           !s : int set.
             distribution p (m n k) s =
             Normal
               ((&(CARD (s INTER integer_interval n)) : real) *
                inv (&n : real))) /\
        indep_vars
          p
          (\i : num # num. m (FST i) (SND i))
          (\i : num # num. (UNIV, POW UNIV))
          UNIV /\
        (!n : num.
           0 < n
           ==>
           !w : 'omega. a n 0 w = 1) /\
        (!n k : num.
           !w : 'omega.
             0 < n
             ==>
             a n (k + 1) w =
             if m n k w > a n k w then
               a n k w + 1
             else if m n k w = a n k w then
               a n k w
             else
               a n k w - 1)
        ==>
        ((((\n : num.
               (real
                  (expectation
                    p
                    (\w : 'omega.
                       Normal (real_of_int (a n n w)))) *
                inv (&n : real) : real)) : num -> real) -->
          ((1 - exp (-2)) * inv (2 : real) : real))
         sequentially)``;
