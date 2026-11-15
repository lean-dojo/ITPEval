(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q420714, "Akra–Bazzi theorem": a recurrence with positive coefficients,
  contracting branches, polynomially growing toll, and lower-order rounding
  errors is big-O of its Akra-Bazzi asymptotic bound. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory transcTheory;

val q420714_real_rpow_def = new_definition (
  "q420714_real_rpow_def",
  ``q420714_real_rpow (x : real) (p : real) =
      if x = 0 then if p = 0 then 1 else 0 else x rpow p``);

val q420714_finite_sum_def = new_definition (
  "q420714_finite_sum_def",
  ``q420714_finite_sum (s : 'i set) (f : 'i -> real) =
      ITSET (\i acc. f i + acc) s 0``);

val q420714_little_o_def = new_definition (
  "q420714_little_o_def",
  ``q420714_little_o (f : num -> real) (h : num -> real) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> abs (f n) <= epsilon * abs (h n)``);

val q420714_grows_polynomially_def = new_definition (
  "q420714_grows_polynomially_def",
  ``q420714_grows_polynomially (g : real -> real) <=>
      !beta : real.
        0 < beta /\ beta < 1 ==>
        ?c1 c2 : real.
          0 < c1 /\ 0 < c2 /\
          ?X : real. !x : real.
            X <= x ==>
            !u : real.
              beta * x <= u /\ u <= x ==>
              c1 * g x <= g u /\ g u <= c2 * g x``);

val q420714_akra_bazzi_recurrence_def = new_definition (
  "q420714_akra_bazzi_recurrence_def",
  ``q420714_akra_bazzi_recurrence
      (T : num -> real) (g : real -> real)
      (a : 'i -> real) (b : 'i -> real)
      (r : 'i -> num -> num) <=>
      ?n0 : num.
        0 < n0 /\
        (!i : 'i. 0 < a i) /\
        (!i : 'i. 0 < b i) /\
        (!i : 'i. b i < 1) /\
        (!x : real. 0 <= x ==> 0 <= g x) /\
        q420714_grows_polynomially g /\
        (!n : num.
          n0 <= n ==>
          T n =
            q420714_finite_sum UNIV
              (\i : 'i. a i * T (r i n)) +
            g (&n)) /\
        (!n : num. n < n0 ==> 0 < T n) /\
        (!i : 'i. !n : num. n0 <= n ==> r i n < n) /\
        (!i : 'i.
          q420714_little_o
            (\n : num. &(r i n) - b i * &n)
            (\n : num. &n / ((ln (&n)) pow 2)))``);

val q420714_exponent_def = new_definition (
  "q420714_exponent_def",
  ``q420714_exponent (a : 'i -> real) (b : 'i -> real) =
      @p : real.
        q420714_finite_sum UNIV
          (\i : 'i. a i * q420714_real_rpow (b i) p) = 1``);

val q420714_asymp_bound_def = new_definition (
  "q420714_asymp_bound_def",
  ``q420714_asymp_bound
      (g : real -> real) (a : 'i -> real) (b : 'i -> real)
      (n : num) =
      let p = q420714_exponent a b in
        q420714_real_rpow (&n) p +
        q420714_real_rpow (&n) p *
          ITSET
            (\u acc.
              g (&u) /
                q420714_real_rpow (&u) (p + 1) +
              acc)
            (count n) 0``);

val q420714_is_big_o_def = new_definition (
  "q420714_is_big_o_def",
  ``q420714_is_big_o (f : num -> real) (h : num -> real) <=>
      ?C : real. ?N : num. !n : num.
        N <= n ==> abs (f n) <= C * abs (h n)``);

val AkraBazziRecurrence_isBigO_asympBound =
  ``!(T : num -> real) (g : real -> real)
      (a : 'i -> real) (b : 'i -> real)
      (r : 'i -> num -> num).
      FINITE (UNIV : 'i set) /\
      q420714_akra_bazzi_recurrence T g a b r
      ==>
      q420714_is_big_o T (q420714_asymp_bound g a b)``;
