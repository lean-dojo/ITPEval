(*
  Statement-only formalization of PutnamBench artifact putnam_1968_b1:
  the probability that the minimum of two finite-range integer-valued random
  variables equals k is the sum of their point probabilities minus the
  probability that their maximum equals k. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory integerTheory realTheory;
open extrealTheory measureTheory probabilityTheory;

val putnam_1968_b1 =
  ``!(p : 'a p_space) (X Y : 'a -> int) (k : int).
      prob_space p /\
      p_space p = UNIV /\
      random_variable X p (UNIV, POW UNIV) /\
      random_variable Y p (UNIV, POW UNIV) /\
      FINITE (IMAGE X UNIV) /\
      FINITE (IMAGE Y UNIV)
      ==>
      real
        (prob p
          {w : 'a | int_min (X w) (Y w) = k}) =
      real (prob p {w : 'a | X w = k}) +
      real (prob p {w : 'a | Y w = k}) -
      real
        (prob p
          {w : 'a | int_max (X w) (Y w) = k})``;
