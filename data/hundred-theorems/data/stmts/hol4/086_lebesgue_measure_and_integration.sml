(*
  Statement-only formalization of "Lebesgue Measure and Integration" from Hundred Theorems
  item 086. It states the construction and fundamental normalization, monotonicity, indicator,
  linearity, and monotone-convergence laws for Lebesgue measure and integration. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory;
open lebesgueTheory lebesgue_measureTheory;

val lebesgue_measure_normalization =
  ``measure_space lebesgue /\
    (!a b.
       a <= b ==>
       measure lebesgue (interval [a,b]) = Normal (b - a)) /\
    (!s.
       s IN subsets borel ==>
       measure lebesgue s = lambda s)``;

val lower_lebesgue_integral_characterization =
  ``!(m : 'a m_space) (f : 'a -> extreal).
      pos_fn_integral m f =
        sup
          {r |
             ?g.
               r IN psfis m g /\
               !x. x IN m_space m ==> g x <= f x}``;

val lower_lebesgue_integral_indicator_and_monotonicity =
  ``!(m : 'a m_space) (s : 'a set)
      (f : 'a -> extreal) (g : 'a -> extreal).
      measure_space m /\
      s IN measurable_sets m /\
      (!x. x IN m_space m ==> 0 <= f x) /\
      (!x. x IN m_space m ==> f x <= g x)
      ==>
      pos_fn_integral m (indicator_fn s) = measure m s /\
      pos_fn_integral m f <= pos_fn_integral m g``;

val lower_lebesgue_monotone_convergence =
  ``!(m : 'a m_space) (f : 'a -> extreal)
      (fi : num -> 'a -> extreal).
      measure_space m /\
      (!i. fi i IN measurable (m_space m, measurable_sets m) Borel) /\
      (!i x. x IN m_space m ==> 0 <= fi i x) /\
      (!x. x IN m_space m ==> mono_increasing (\i. fi i x)) /\
      (!x.
         x IN m_space m ==>
         sup (IMAGE (\i. fi i x) UNIV) = f x)
      ==>
      pos_fn_integral m f =
        sup (IMAGE (\i. pos_fn_integral m (fi i)) UNIV)``;

val lebesgue_integral_linearity_and_monotonicity =
  ``!(m : 'a m_space) (f g : 'a -> real).
      measure_space m /\
      integrable m (Normal o f) /\
      integrable m (Normal o g)
      ==>
      integrable m (\x. Normal (f x + g x)) /\
      integral m (\x. Normal (f x + g x)) =
        integral m (Normal o f) + integral m (Normal o g) /\
      ((!x. x IN m_space m ==> f x <= g x) ==>
       integral m (Normal o f) <= integral m (Normal o g))``;
