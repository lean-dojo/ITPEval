(*
  Statement-only formalization of "Fair Games Theorem (Optional Stopping)"
  from Hundred Theorems item 062. It characterizes strongly adapted,
  integrable real-valued submartingales by monotonicity of expected stopped
  values at ordered bounded stopping times. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;
open extrealTheory sigma_algebraTheory measureTheory borelTheory;
open lebesgueTheory martingaleTheory probabilityTheory;

val fair_games_theorem_optional_stopping =
  ``!(m : 'a m_space) (a : num -> 'a algebra)
      (f : num -> 'a -> real).
      let strongly_adapted =
        \g : num -> 'a -> real.
          !n. g n IN measurable (a n) borel
      in
      let is_stopping_time =
        \tau : 'a -> num option.
          !n.
            ({x | ?k. tau x = SOME k /\ k <= n} INTER m_space m)
              IN subsets (a n)
      in
      let stopping_time_le =
        \tau pi : 'a -> num option.
          !x. x IN m_space m ==>
              case pi x of
                NONE => T
              | SOME j =>
                  case tau x of
                    NONE => F
                  | SOME i => i <= j
      in
      let bounded_stopping_time =
        \pi : 'a -> num option.
          ?N. !x. x IN m_space m ==>
                case pi x of
                  NONE => F
                | SOME n => n <= N
      in
      let stopped_value =
        \g : num -> 'a -> real.
        \tau : 'a -> num option.
        \x.
          case tau x of
            NONE => 0
          | SOME n => g n x
      in
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
