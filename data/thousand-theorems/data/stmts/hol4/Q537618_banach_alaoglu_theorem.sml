(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q537618 (thousand-theorems__hol4__Q537618), "Banach–Alaoglu theorem":
  over a proper nontrivially normed field, the polar of a neighborhood of zero
  in a seminormed space is compact in the weak-star topology on the continuous
  dual. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory pred_setTheory;

val q537618_nontrivially_normed_field_def = new_definition (
  "q537618_nontrivially_normed_field_def",
  ``q537618_nontrivially_normed_field
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

val q537618_seminormed_add_comm_group_def = new_definition (
  "q537618_seminormed_add_comm_group_def",
  ``q537618_seminormed_add_comm_group
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (normE : 'e -> real) <=>
      (!x y. addE x y = addE y x) /\
      (!x y z. addE (addE x y) z = addE x (addE y z)) /\
      (!x. addE x zeroE = x) /\
      (!x. addE x (negE x) = zeroE) /\
      (!x. 0 <= normE x) /\
      normE zeroE = 0 /\
      (!x. normE (negE x) = normE x) /\
      (!x y. normE (addE x y) <= normE x + normE y)``);

val q537618_normed_space_def = new_definition (
  "q537618_normed_space_def",
  ``q537618_normed_space
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

val q537618_scalar_open_def = new_definition (
  "q537618_scalar_open_def",
  ``q537618_scalar_open
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) (u : 'k set) <=>
      !a. a IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !b. normK (addK b (negK a)) < epsilon ==> b IN u``);

val q537618_scalar_compact_def = new_definition (
  "q537618_scalar_compact_def",
  ``q537618_scalar_compact
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) (k : 'k set) <=>
      !cover : ('k set) set.
        (!u. u IN cover ==> q537618_scalar_open addK negK normK u) /\
        k SUBSET BIGUNION cover
        ==>
        ?subcover : ('k set) set.
          FINITE subcover /\
          subcover SUBSET cover /\
          k SUBSET BIGUNION subcover``);

val q537618_proper_space_def = new_definition (
  "q537618_proper_space_def",
  ``q537618_proper_space
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) <=>
      !a : 'k. !r : real.
        q537618_scalar_compact addK negK normK
          {b : 'k | normK (addK b (negK a)) <= r}``);

val q537618_continuous_linear_functional_def = new_definition (
  "q537618_continuous_linear_functional_def",
  ``q537618_continuous_linear_functional
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real) (f : 'e -> 'k) <=>
      (!x y. f (addE x y) = addK (f x) (f y)) /\
      (!a x. f (smulE a x) = mulK a (f x)) /\
      ?C : real.
        0 <= C /\
        !x. normK (f x) <= C * normE x``);

val q537618_dual_def = new_definition (
  "q537618_dual_def",
  ``q537618_dual
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real) =
      {f : 'e -> 'k |
        q537618_continuous_linear_functional
          addK mulK normK addE smulE normE f}``);

val q537618_polar_def = new_definition (
  "q537618_polar_def",
  ``q537618_polar
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real) (s : 'e set) =
      {f : 'e -> 'k |
        f IN q537618_dual addK mulK normK addE smulE normE /\
        !x. x IN s ==> normK (f x) <= 1}``);

val q537618_weak_star_open_def = new_definition (
  "q537618_weak_star_open_def",
  ``q537618_weak_star_open
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) (dual : ('e -> 'k) set)
      (u : ('e -> 'k) set) <=>
      u SUBSET dual /\
      !f. f IN u ==>
        ?d : 'e set. ?epsilon : real.
          FINITE d /\
          0 < epsilon /\
          !g.
            g IN dual /\
            (!x. x IN d ==>
              normK (addK (g x) (negK (f x))) < epsilon)
            ==>
            g IN u``);

val q537618_weak_star_compact_def = new_definition (
  "q537618_weak_star_compact_def",
  ``q537618_weak_star_compact
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) (dual : ('e -> 'k) set)
      (k : ('e -> 'k) set) <=>
      k SUBSET dual /\
      !cover : (('e -> 'k) set) set.
        (!u. u IN cover ==>
          q537618_weak_star_open addK negK normK dual u) /\
        k SUBSET BIGUNION cover
        ==>
        ?subcover : (('e -> 'k) set) set.
          FINITE subcover /\
          subcover SUBSET cover /\
          k SUBSET BIGUNION subcover``);

val q537618_mem_nhds_zero_def = new_definition (
  "q537618_mem_nhds_zero_def",
  ``q537618_mem_nhds_zero (normE : 'e -> real) (s : 'e set) <=>
      ?epsilon : real.
        0 < epsilon /\
        !x. normE x < epsilon ==> x IN s``);

val WeakDual_isCompact_polar =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real) (s : 'e set).
      q537618_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q537618_proper_space addK negK normK /\
      q537618_seminormed_add_comm_group zeroE addE negE normE /\
      q537618_normed_space
        zeroK oneK addK mulK normK zeroE addE smulE normE /\
      q537618_mem_nhds_zero normE s
      ==>
      q537618_weak_star_compact addK negK normK
        (q537618_dual addK mulK normK addE smulE normE)
        (q537618_polar addK mulK normK addE smulE normE s)``;
