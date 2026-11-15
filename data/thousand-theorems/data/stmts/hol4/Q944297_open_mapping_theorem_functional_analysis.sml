(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q944297 (thousand-theorems__hol4__Q944297), "Open mapping theorem
  (functional analysis)": a surjective continuous semilinear map between
  Banach spaces over isometrically isomorphic nontrivially normed fields is
  an open map. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory pred_setTheory;

val q944297_nontrivially_normed_field_def = new_definition (
  "q944297_nontrivially_normed_field_def",
  ``q944297_nontrivially_normed_field
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

val q944297_normed_add_comm_group_def = new_definition (
  "q944297_normed_add_comm_group_def",
  ``q944297_normed_add_comm_group
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (norm : 'a -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q944297_normed_space_def = new_definition (
  "q944297_normed_space_def",
  ``q944297_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real) <=>
      (!x. smulE oneK x = x) /\
      (!a b x. smulE (mulK a b) x = smulE a (smulE b x)) /\
      (!a b x. smulE (addK a b) x =
                 addE (smulE a x) (smulE b x)) /\
      (!a x y. smulE a (addE x y) =
                 addE (smulE a x) (smulE a y)) /\
      (!x. smulE zeroK x = zeroE) /\
      (!a. smulE a zeroE = zeroE) /\
      (!a x. normE (smulE a x) = normK a * normE x)``);

val q944297_ring_hom_def = new_definition (
  "q944297_ring_hom_def",
  ``q944297_ring_hom
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroL : 'l) (oneL : 'l)
      (addL : 'l -> 'l -> 'l) (mulL : 'l -> 'l -> 'l)
      (sigma : 'k -> 'l) <=>
      sigma zeroK = zeroL /\
      sigma oneK = oneL /\
      (!a b. sigma (addK a b) = addL (sigma a) (sigma b)) /\
      (!a b. sigma (mulK a b) = mulL (sigma a) (sigma b))``);

val q944297_isometric_ring_hom_inv_pair_def = new_definition (
  "q944297_isometric_ring_hom_inv_pair_def",
  ``q944297_isometric_ring_hom_inv_pair
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroL : 'l) (oneL : 'l)
      (addL : 'l -> 'l -> 'l) (mulL : 'l -> 'l -> 'l)
      (normL : 'l -> real)
      (sigma : 'k -> 'l) (sigma' : 'l -> 'k) <=>
      q944297_ring_hom
        zeroK oneK addK mulK zeroL oneL addL mulL sigma /\
      q944297_ring_hom
        zeroL oneL addL mulL zeroK oneK addK mulK sigma' /\
      (!a. sigma' (sigma a) = a) /\
      (!b. sigma (sigma' b) = b) /\
      (!a. normL (sigma a) = normK a) /\
      (!b. normK (sigma' b) = normL b)``);

val q944297_tendsto_def = new_definition (
  "q944297_tendsto_def",
  ``q944297_tendsto
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) (x : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q944297_cauchy_def = new_definition (
  "q944297_cauchy_def",
  ``q944297_cauchy
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q944297_complete_space_def = new_definition (
  "q944297_complete_space_def",
  ``q944297_complete_space
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) <=>
      !u : num -> 'a.
        q944297_cauchy add neg norm u ==>
        ?x : 'a. q944297_tendsto add neg norm u x``);

val q944297_continuous_semilinear_map_def = new_definition (
  "q944297_continuous_semilinear_map_def",
  ``q944297_continuous_semilinear_map
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'l -> 'f -> 'f) (normF : 'f -> real)
      (sigma : 'k -> 'l) (g : 'e -> 'f) <=>
      (!x y. g (addE x y) = addF (g x) (g y)) /\
      (!a x. g (smulE a x) = smulF (sigma a) (g x)) /\
      (!x : 'e. !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y : 'e.
            normE (addE y (negE x)) < delta ==>
            normF (addF (g y) (negF (g x))) < epsilon)``);

val q944297_is_open_def = new_definition (
  "q944297_is_open_def",
  ``q944297_is_open
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (s : 'a set) <=>
      !x : 'a.
        x IN s ==>
        ?epsilon : real.
          0 < epsilon /\
          !y : 'a.
            norm (add y (neg x)) < epsilon ==> y IN s``);

val q944297_is_open_map_def = new_definition (
  "q944297_is_open_map_def",
  ``q944297_is_open_map
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (normF : 'f -> real) (g : 'e -> 'f) <=>
      !s : 'e set.
        q944297_is_open addE negE normE s ==>
        q944297_is_open addF negF normF (IMAGE g s)``);

val ContinuousLinearMap_isOpenMap =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroL : 'l) (oneL : 'l)
      (addL : 'l -> 'l -> 'l) (mulL : 'l -> 'l -> 'l)
      (negL : 'l -> 'l) (invL : 'l -> 'l)
      (normL : 'l -> real)
      (sigma : 'k -> 'l) (sigma' : 'l -> 'k)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : 'l -> 'f -> 'f)
      (normF : 'f -> real) (g : 'e -> 'f).
      q944297_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q944297_nontrivially_normed_field
        zeroL oneL addL mulL negL invL normL /\
      q944297_isometric_ring_hom_inv_pair
        zeroK oneK addK mulK normK
        zeroL oneL addL mulL normL sigma sigma' /\
      q944297_normed_add_comm_group zeroE addE negE normE /\
      q944297_normed_space
        zeroK oneK addK mulK normK zeroE addE smulE normE /\
      q944297_complete_space addE negE normE /\
      q944297_normed_add_comm_group zeroF addF negF normF /\
      q944297_normed_space
        zeroL oneL addL mulL normL zeroF addF smulF normF /\
      q944297_complete_space addF negF normF /\
      q944297_continuous_semilinear_map
        addE negE smulE normE addF negF smulF normF sigma g /\
      (!y : 'f. ?x : 'e. g x = y)
      ==>
      q944297_is_open_map
        addE negE normE addF negF normF g``;
