(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q931001 (thousand-theorems__hol4__Q931001), "Inverse function theorem":
  over a nontrivially normed field, a map from a complete normed space with
  an invertible strict Frechet derivative at a point has a choice-constructed
  local inverse whose strict derivative at the image point is the inverse
  continuous linear map. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val q931001_nontrivially_normed_field_def = new_definition (
  "q931001_nontrivially_normed_field_def",
  ``q931001_nontrivially_normed_field
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real) <=>
      zeroK <> oneK /\
      (!a b. addK a b = addK b a) /\
      (!a b c. addK (addK a b) c = addK a (addK b c)) /\
      (!a. addK a zeroK = a) /\
      (!a. addK a (negK a) = zeroK) /\
      (!a b. mulK a b = mulK b a) /\
      (!a b c. mulK (mulK a b) c = mulK a (mulK b c)) /\
      (!a. mulK a oneK = a) /\
      (!a b c.
        mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
      invK zeroK = zeroK /\
      (!a. a <> zeroK ==> mulK a (invK a) = oneK) /\
      (!a. 0 <= normK a) /\
      (!a. (normK a = 0) <=> (a = zeroK)) /\
      (!a. normK (negK a) = normK a) /\
      (!a b. normK (addK a b) <= normK a + normK b) /\
      (!a b. normK (mulK a b) = normK a * normK b) /\
      (?a. 1 < normK a)``);

val q931001_normed_add_comm_group_def = new_definition (
  "q931001_normed_add_comm_group_def",
  ``q931001_normed_add_comm_group
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (norm : 'e -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      norm zero = 0 /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q931001_normed_space_def = new_definition (
  "q931001_normed_space_def",
  ``q931001_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real) <=>
      (!x. smulE oneK x = x) /\
      (!a b x. smulE (mulK a b) x = smulE a (smulE b x)) /\
      (!a b x. smulE (addK a b) x = addE (smulE a x) (smulE b x)) /\
      (!a x y. smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
      (!x. smulE zeroK x = zeroE) /\
      (!a. smulE a zeroE = zeroE) /\
      (!a x. normE (smulE a x) = normK a * normE x)``);

val q931001_tendsto_def = new_definition (
  "q931001_tendsto_def",
  ``q931001_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q931001_cauchy_def = new_definition (
  "q931001_cauchy_def",
  ``q931001_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q931001_complete_space_def = new_definition (
  "q931001_complete_space_def",
  ``q931001_complete_space
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q931001_cauchy add neg norm u ==>
        ?x : 'e. q931001_tendsto add neg norm u x``);

val q931001_continuous_linear_map_def = new_definition (
  "q931001_continuous_linear_map_def",
  ``q931001_continuous_linear_map
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real) (L : 'e -> 'f) <=>
      (!x y. L (addE x y) = addF (L x) (L y)) /\
      (!a x. L (smulE a x) = smulF a (L x)) /\
      ?C : real.
        0 <= C /\
        !x. normF (L x) <= C * normE x``);

val q931001_continuous_linear_equiv_def = new_definition (
  "q931001_continuous_linear_equiv_def",
  ``q931001_continuous_linear_equiv
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real)
      (forward : 'e -> 'f) (inverse : 'f -> 'e) <=>
      q931001_continuous_linear_map
        addE smulE normE addF smulF normF forward /\
      q931001_continuous_linear_map
        addF smulF normF addE smulE normE inverse /\
      (!x. inverse (forward x) = x) /\
      (!y. forward (inverse y) = y)``);

val q931001_has_strict_fderiv_at_def = new_definition (
  "q931001_has_strict_fderiv_at_def",
  ``q931001_has_strict_fderiv_at
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (f : 'e -> 'f) (f' : 'e -> 'f) (a : 'e) <=>
      q931001_continuous_linear_map
        addE smulE normE addF smulF normF f' /\
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !x y : 'e.
            normE (addE x (negE a)) < delta /\
            normE (addE y (negE a)) < delta
            ==>
            normF
              (addF
                (addF (f x) (negF (f y)))
                (negF (f' (addE x (negE y))))) <=
            epsilon * normE (addE x (negE y))``);

val q931001_open_set_def = new_definition (
  "q931001_open_set_def",
  ``q931001_open_set
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (s : 'a -> bool) <=>
      !x.
        x IN s ==>
        ?radius : real.
          0 < radius /\
          !y.
            norm (add y (neg x)) < radius ==>
            y IN s``);

val q931001_continuous_on_def = new_definition (
  "q931001_continuous_on_def",
  ``q931001_continuous_on
      (addA : 'a -> 'a -> 'a) (negA : 'a -> 'a)
      (normA : 'a -> real)
      (addB : 'b -> 'b -> 'b) (negB : 'b -> 'b)
      (normB : 'b -> real)
      (source : 'a -> bool) (f : 'a -> 'b) <=>
      !x.
        x IN source ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              y IN source /\
              normA (addA y (negA x)) < delta
              ==>
              normB (addB (f y) (negB (f x))) < epsilon``);

val q931001_open_partial_homeomorph_def = new_definition (
  "q931001_open_partial_homeomorph_def",
  ``q931001_open_partial_homeomorph
      (addA : 'a -> 'a -> 'a) (negA : 'a -> 'a)
      (normA : 'a -> real)
      (addB : 'b -> 'b -> 'b) (negB : 'b -> 'b)
      (normB : 'b -> real)
      (forward : 'a -> 'b) (pt : 'a)
      (h : ('a -> bool) # (('b -> bool) # ('b -> 'a))) <=>
      let source = FST h in
      let target = FST (SND h) in
      let inverse = SND (SND h) in
        q931001_open_set addA negA normA source /\
        q931001_open_set addB negB normB target /\
        pt IN source /\
        forward pt IN target /\
        (!x.
          x IN source ==>
          forward x IN target /\ inverse (forward x) = x) /\
        (!y.
          y IN target ==>
          inverse y IN source /\ forward (inverse y) = y) /\
        q931001_continuous_on
          addA negA normA addB negB normB source forward /\
        q931001_continuous_on
          addB negB normB addA negA normA target inverse``);

val q931001_to_open_partial_homeomorph_def = new_definition (
  "q931001_to_open_partial_homeomorph_def",
  ``q931001_to_open_partial_homeomorph
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (f : 'e -> 'f) (f' : 'e -> 'f) (f'inv : 'f -> 'e)
      (a : 'e) =
      @h : ('e -> bool) # (('f -> bool) # ('f -> 'e)).
        q931001_has_strict_fderiv_at
          addE negE smulE normE addF negF smulF normF f f' a /\
        q931001_continuous_linear_equiv
          addE smulE normE addF smulF normF f' f'inv /\
        q931001_open_partial_homeomorph
          addE negE normE addF negF normF f a h``);

val q931001_local_inverse_def = new_definition (
  "q931001_local_inverse_def",
  ``q931001_local_inverse
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (f : 'e -> 'f) (f' : 'e -> 'f) (f'inv : 'f -> 'e)
      (a : 'e) =
      SND
        (SND
          (q931001_to_open_partial_homeomorph
            addE negE smulE normE
            addF negF smulF normF
            f f' f'inv a))``);

val HasStrictFDerivAt_to_localInverse =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real)
      (f : 'e -> 'f) (f' : 'e -> 'f) (f'inv : 'f -> 'e)
      (a : 'e).
      q931001_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q931001_normed_add_comm_group zeroE addE negE normE /\
      q931001_normed_space
        zeroK oneK addK mulK normK zeroE addE smulE normE /\
      q931001_complete_space addE negE normE /\
      q931001_normed_add_comm_group zeroF addF negF normF /\
      q931001_normed_space
        zeroK oneK addK mulK normK zeroF addF smulF normF /\
      q931001_continuous_linear_equiv
        addE smulE normE addF smulF normF f' f'inv /\
      q931001_has_strict_fderiv_at
        addE negE smulE normE addF negF smulF normF f f' a
      ==>
      q931001_has_strict_fderiv_at
        addF negF smulF normF addE negE smulE normE
        (q931001_local_inverse
          addE negE smulE normE addF negF smulF normF
          f f' f'inv a)
        f'inv (f a)``;
