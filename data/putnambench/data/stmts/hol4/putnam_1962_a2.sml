(*
  Statement-only formalization of PutnamBench artifact putnam_1962_a2:
  classification of nonnegative real functions whose average on each interval
  from zero is the geometric mean of their endpoint values. The solution is
  the published rational-square family. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory transcTheory;
open extrealTheory measureTheory lebesgueTheory lebesgue_measureTheory;

val putnam_1962_a2 =
  ``let interval_average =
      \f x.
        let restricted =
          \t : real.
            Normal (f t) * indicator_fn (interval [0, x]) t
        in
          if lebesgue$integrable lebesgue restricted then
            real (lebesgue$integral lebesgue restricted) / x
          else
            0
    in
    let solution =
      \g : real -> real.
        ?a c : real.
          0 <= a /\
          g = (\x. a / (1 - c * x) pow 2)
    in
    let has_average_property =
      \s (f : real -> real).
        (!x : real. 0 <= f x) /\
        (!x : real.
           x IN s ==>
           interval_average f x = sqrt (f 0 * f x))
    in
      (!f : real -> real.
         (has_average_property {x : real | 0 < x} f ==>
          ?g : real -> real.
            solution g /\
            !x : real. 0 <= x ==> f x = g x) /\
         (!e : real.
            0 < e /\
            has_average_property {x : real | 0 < x /\ x < e} f
            ==>
            ?g : real -> real.
              solution g /\
              !x : real. 0 <= x /\ x < e ==> f x = g x)) /\
      (!f : real -> real.
         solution f ==>
         has_average_property {x : real | 0 < x} f \/
         ?e : real.
           0 < e /\
           has_average_property {x : real | 0 < x /\ x < e} f)``;
