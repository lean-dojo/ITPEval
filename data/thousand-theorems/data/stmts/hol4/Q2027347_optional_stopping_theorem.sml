(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q2027347, "Optional stopping theorem": a strongly adapted integrable
  real-valued process is a submartingale exactly when expected stopped values
  are monotone at ordered bounded stopping times. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open extrealTheory sigma_algebraTheory measureTheory borelTheory;
open lebesgueTheory martingaleTheory probabilityTheory;

val optional_stopping_theorem =
  ``!(m : 'a m_space) (a : num -> 'a algebra)
      (f : num -> 'a -> real).
      let strongly_adapted =
        \g : num -> 'a -> real.
          !n. g n IN measurable (a n) borel
      in
      let is_stopping_time =
        \tau : 'a -> num option.
          !n.
            {x | ?k. tau x = SOME k /\ k <= n} IN subsets (a n)
      in
      let stopping_time_le =
        \tau pi : 'a -> num option.
          !x.
            case pi x of
              NONE => T
            | SOME j =>
                case tau x of
                  NONE => F
                | SOME i => i <= j
      in
      let bounded_stopping_time =
        \pi : 'a -> num option.
          ?N. !x.
            case pi x of
              NONE => F
            | SOME n => n <= N
      in
      let stopped_value =
        \g : num -> 'a -> real.
        \tau : 'a -> num option.
        \x.
          case tau x of
            NONE => g 0 x
          | SOME n => g n x
      in
        m_space m = UNIV /\
        sigma_finite_filtered_measure_space m a /\
        strongly_adapted f /\
        (!n. integrable m (Normal o f n))
        ==>
        (sub_martingale m a (\n x. Normal (f n x)) <=>
         !tau pi.
           is_stopping_time tau /\
           is_stopping_time pi /\
           stopping_time_le tau pi /\
           bounded_stopping_time pi
           ==>
           expectation m (Normal o stopped_value f tau) <=
           expectation m (Normal o stopped_value f pi))``;
