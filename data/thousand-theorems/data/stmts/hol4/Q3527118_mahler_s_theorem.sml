(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527118 (thousand-theorems__hol4__Q3527118), "Mahler's theorem": the
  Mahler series of a continuous function from the p-adic integers to a
  complete nonarchimedean normed module, with iterated forward differences
  as coefficients, sums uniformly to the function. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory combinTheory combinatoricsTheory;
open pred_setTheory realTheory;

val q3527118_padicVal_def = new_definition (
  "q3527118_padicVal_def",
  ``q3527118_padicVal (p : num) (n : num) =
      if n = 0 then 0
      else MAX_SET {k : num | (p EXP k) divides n}``);

val q3527118_nat_padic_norm_def = new_definition (
  "q3527118_nat_padic_norm_def",
  ``q3527118_nat_padic_norm (p : num) (n : num) =
      if n = 0 then 0
      else inv (&(p EXP q3527118_padicVal p n))``);

val q3527118_sub_def = new_definition (
  "q3527118_sub_def",
  ``q3527118_sub
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a) (x : 'a) y =
      add x (neg y)``);

val q3527118_cauchy_def = new_definition (
  "q3527118_cauchy_def",
  ``q3527118_cauchy
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (q3527118_sub add neg (u m) (u n)) < epsilon``);

val q3527118_tendsto_def = new_definition (
  "q3527118_tendsto_def",
  ``q3527118_tendsto
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) (x : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==>
          norm (q3527118_sub add neg (u n) x) < epsilon``);

val q3527118_complete_def = new_definition (
  "q3527118_complete_def",
  ``q3527118_complete
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) <=>
      !u : num -> 'a.
        q3527118_cauchy add neg norm u ==>
        ?x : 'a. q3527118_tendsto add neg norm u x``);

val q3527118_continuous_def = new_definition (
  "q3527118_continuous_def",
  ``q3527118_continuous
      (addA : 'a -> 'a -> 'a) (negA : 'a -> 'a)
      (normA : 'a -> real)
      (addB : 'b -> 'b -> 'b) (negB : 'b -> 'b)
      (normB : 'b -> real) (f : 'a -> 'b) <=>
      !x : 'a. !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y : 'a.
            normA (q3527118_sub addA negA y x) < delta ==>
            normB (q3527118_sub addB negB (f y) (f x)) < epsilon``);

val q3527118_padic_int_context_def = new_definition (
  "q3527118_padic_int_context_def",
  ``q3527118_padic_int_context
      (p : num)
      (zeroZ : 'z) (oneZ : 'z)
      (addZ : 'z -> 'z -> 'z) (mulZ : 'z -> 'z -> 'z)
      (negZ : 'z -> 'z) (normZ : 'z -> real)
      (natCast : num -> 'z) <=>
      zeroZ <> oneZ /\
      (!x y. addZ x y = addZ y x) /\
      (!x y z. addZ (addZ x y) z = addZ x (addZ y z)) /\
      (!x. addZ zeroZ x = x) /\
      (!x. addZ (negZ x) x = zeroZ) /\
      (!x y. mulZ x y = mulZ y x) /\
      (!x y z. mulZ (mulZ x y) z = mulZ x (mulZ y z)) /\
      (!x. mulZ oneZ x = x) /\
      (!x y z. mulZ x (addZ y z) = addZ (mulZ x y) (mulZ x z)) /\
      natCast 0 = zeroZ /\
      (!n. natCast (SUC n) = addZ (natCast n) oneZ) /\
      (!x. 0 <= normZ x) /\
      (!x. normZ x = 0 <=> x = zeroZ) /\
      (!x. normZ (negZ x) = normZ x) /\
      (!x y. normZ (mulZ x y) = normZ x * normZ y) /\
      (!x y.
        normZ (addZ x y) <= max (normZ x) (normZ y)) /\
      (!x. normZ x <= 1) /\
      (!n. normZ (natCast n) = q3527118_nat_padic_norm p n) /\
      (!x : 'z. !epsilon : real.
        0 < epsilon ==>
        ?n : num.
          normZ (q3527118_sub addZ negZ x (natCast n)) < epsilon) /\
      q3527118_complete addZ negZ normZ``);

val q3527118_normed_module_context_def = new_definition (
  "q3527118_normed_module_context_def",
  ``q3527118_normed_module_context
      (zeroZ : 'z) (oneZ : 'z)
      (addZ : 'z -> 'z -> 'z) (mulZ : 'z -> 'z -> 'z)
      (normZ : 'z -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real) (smul : 'z -> 'e -> 'e) <=>
      (!x y. addE x y = addE y x) /\
      (!x y z. addE (addE x y) z = addE x (addE y z)) /\
      (!x. addE zeroE x = x) /\
      (!x. addE (negE x) x = zeroE) /\
      (!x. 0 <= normE x) /\
      (!x. normE x = 0 <=> x = zeroE) /\
      (!x. normE (negE x) = normE x) /\
      (!x y.
        normE (addE x y) <= max (normE x) (normE y)) /\
      (!x. smul oneZ x = x) /\
      (!a b x. smul (mulZ a b) x = smul a (smul b x)) /\
      (!a b x. smul (addZ a b) x = addE (smul a x) (smul b x)) /\
      (!a x y. smul a (addE x y) = addE (smul a x) (smul a y)) /\
      (!x. smul zeroZ x = zeroE) /\
      (!a. smul a zeroE = zeroE) /\
      (!a x. normE (smul a x) <= normZ a * normE x) /\
      q3527118_complete addE negE normE``);

val q3527118_mahler_characterizes_def = new_definition (
  "q3527118_mahler_characterizes_def",
  ``q3527118_mahler_characterizes
      (addZ : 'z -> 'z -> 'z) (negZ : 'z -> 'z)
      (normZ : 'z -> real) (natCast : num -> 'z)
      (n : num) (g : 'z -> 'z) <=>
      q3527118_continuous
        addZ negZ normZ addZ negZ normZ g /\
      !m : num. g (natCast m) = natCast (binomial m n)``);

val q3527118_mahler_def = new_definition (
  "q3527118_mahler_def",
  ``q3527118_mahler
      (addZ : 'z -> 'z -> 'z) (negZ : 'z -> 'z)
      (normZ : 'z -> real) (natCast : num -> 'z) (n : num) =
      @g : 'z -> 'z.
        q3527118_mahler_characterizes
          addZ negZ normZ natCast n g``);

val q3527118_fwdDiff_def = new_definition (
  "q3527118_fwdDiff_def",
  ``q3527118_fwdDiff
      (addZ : 'z -> 'z -> 'z) (oneZ : 'z)
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (g : 'z -> 'e) (x : 'z) =
      q3527118_sub addE negE (g (addZ x oneZ)) (g x)``);

val q3527118_fwdDiff_iter_zero_def = new_definition (
  "q3527118_fwdDiff_iter_zero_def",
  ``q3527118_fwdDiff_iter_zero
      (addZ : 'z -> 'z -> 'z) (oneZ : 'z) (zeroZ : 'z)
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (f : 'z -> 'e) (n : num) =
      FUNPOW (q3527118_fwdDiff addZ oneZ addE negE) n f zeroZ``);

val q3527118_finite_sum_def = new_definition (
  "q3527118_finite_sum_def",
  ``q3527118_finite_sum
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (term : num -> 'a) (s : num set) =
      ITSET (\n acc. add (term n) acc) s zero``);

val q3527118_uniform_hasSum_def = new_definition (
  "q3527118_uniform_hasSum_def",
  ``q3527118_uniform_hasSum
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real)
      (term : num -> 'z -> 'e) (f : 'z -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?s0 : num set.
          FINITE s0 /\
          !s : num set.
            FINITE s /\ s0 SUBSET s ==>
            !x : 'z.
              normE
                (q3527118_sub addE negE
                  (q3527118_finite_sum
                    zeroE addE (\n. term n x) s)
                  (f x)) < epsilon``);

val PadicInt_hasSum_mahler =
  ``!p : num.
      !(zeroZ : 'z) (oneZ : 'z)
        (addZ : 'z -> 'z -> 'z) (mulZ : 'z -> 'z -> 'z)
        (negZ : 'z -> 'z) (normZ : 'z -> real)
        (natCast : num -> 'z)
        (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
        (normE : 'e -> real) (smul : 'z -> 'e -> 'e)
        (f : 'z -> 'e).
        prime p /\
        q3527118_padic_int_context
          p zeroZ oneZ addZ mulZ negZ normZ natCast /\
        q3527118_normed_module_context
          zeroZ oneZ addZ mulZ normZ
          zeroE addE negE normE smul /\
        q3527118_continuous
          addZ negZ normZ addE negE normE f
        ==>
        q3527118_uniform_hasSum
          zeroE addE negE normE
          (\n x.
            smul
              (q3527118_mahler addZ negZ normZ natCast n x)
              (q3527118_fwdDiff_iter_zero
                addZ oneZ zeroZ addE negE f n))
          f``;
