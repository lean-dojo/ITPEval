(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1426292 (thousand-theorems__hol4__Q1426292), "Banach–Steinhaus theorem":
  a pointwise bounded, possibly empty family of continuous semilinear maps
  from a complete seminormed space to a seminormed space is uniformly
  bounded. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val q1426292_nontrivially_normed_field_def = new_definition (
  "q1426292_nontrivially_normed_field_def",
  ``q1426292_nontrivially_normed_field
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

val q1426292_seminormed_add_comm_group_def = new_definition (
  "q1426292_seminormed_add_comm_group_def",
  ``q1426292_seminormed_add_comm_group
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (norm : 'e -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x. 0 <= norm x) /\
      norm zero = 0 /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q1426292_normed_space_def = new_definition (
  "q1426292_normed_space_def",
  ``q1426292_normed_space
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

val q1426292_isometric_ring_hom_def = new_definition (
  "q1426292_isometric_ring_hom_def",
  ``q1426292_isometric_ring_hom
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroL : 'l) (oneL : 'l)
      (addL : 'l -> 'l -> 'l) (mulL : 'l -> 'l -> 'l)
      (normL : 'l -> real) (sigma : 'k -> 'l) <=>
      sigma zeroK = zeroL /\
      sigma oneK = oneL /\
      (!a b. sigma (addK a b) = addL (sigma a) (sigma b)) /\
      (!a b. sigma (mulK a b) = mulL (sigma a) (sigma b)) /\
      (!a. normL (sigma a) = normK a)``);

val q1426292_tendsto_def = new_definition (
  "q1426292_tendsto_def",
  ``q1426292_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q1426292_cauchy_def = new_definition (
  "q1426292_cauchy_def",
  ``q1426292_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q1426292_complete_space_def = new_definition (
  "q1426292_complete_space_def",
  ``q1426292_complete_space
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q1426292_cauchy add neg norm u ==>
        ?x : 'e. q1426292_tendsto add neg norm u x``);

val q1426292_continuous_semilinear_map_def = new_definition (
  "q1426292_continuous_semilinear_map_def",
  ``q1426292_continuous_semilinear_map
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (smulF : 'l -> 'f -> 'f)
      (normF : 'f -> real) (sigma : 'k -> 'l)
      (g : 'e -> 'f) <=>
      (!x y. g (addE x y) = addF (g x) (g y)) /\
      (!a x. g (smulE a x) = smulF (sigma a) (g x)) /\
      ?K : real.
        0 <= K /\
        !x. normF (g x) <= K * normE x``);

val banach_steinhaus =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroL : 'l) (oneL : 'l)
      (addL : 'l -> 'l -> 'l) (mulL : 'l -> 'l -> 'l)
      (negL : 'l -> 'l) (invL : 'l -> 'l)
      (normL : 'l -> real) (sigma : 'k -> 'l)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : 'l -> 'f -> 'f)
      (normF : 'f -> real)
      (index : 'i -> bool) (g : 'i -> 'e -> 'f).
      q1426292_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q1426292_nontrivially_normed_field
        zeroL oneL addL mulL negL invL normL /\
      q1426292_isometric_ring_hom
        zeroK oneK addK mulK normK
        zeroL oneL addL mulL normL sigma /\
      q1426292_seminormed_add_comm_group zeroE addE negE normE /\
      q1426292_normed_space
        zeroK oneK addK mulK normK zeroE addE smulE normE /\
      q1426292_complete_space addE negE normE /\
      q1426292_seminormed_add_comm_group zeroF addF negF normF /\
      q1426292_normed_space
        zeroL oneL addL mulL normL zeroF addF smulF normF /\
      (!i. index i ==>
        q1426292_continuous_semilinear_map
          addE smulE normE addF smulF normF sigma (g i))
      ==>
      ((!x. ?C : real. !i. index i ==> normF (g i x) <= C) ==>
       ?C' : real.
         0 <= C' /\
         !i. index i ==>
           !x. normF (g i x) <= C' * normE x)``;
