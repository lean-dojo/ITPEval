(*
  Statement-only formalization of the Thousand Theorems artifact Q1038716,
  "Identity theorem": two analytic functions from a nontrivially normed field
  to a normed vector space that agree frequently in a punctured neighborhood
  of a point of a preconnected set agree throughout that set. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory realTheory;

val identity_nontrivially_normed_field_def = new_definition (
  "identity_nontrivially_normed_field_def",
  ``identity_nontrivially_normed_field
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

val identity_normed_add_comm_group_def = new_definition (
  "identity_normed_add_comm_group_def",
  ``identity_normed_add_comm_group
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (normE : 'e -> real) <=>
      (!x y. addE x y = addE y x) /\
      (!x y z. addE (addE x y) z = addE x (addE y z)) /\
      (!x. addE x zeroE = x) /\
      (!x. addE x (negE x) = zeroE) /\
      (!x. 0 <= normE x) /\
      (!x. (normE x = 0) <=> (x = zeroE)) /\
      (!x. normE (negE x) = normE x) /\
      (!x y. normE (addE x y) <= normE x + normE y)``);

val identity_normed_space_def = new_definition (
  "identity_normed_space_def",
  ``identity_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smul : 'k -> 'e -> 'e)
      (normK : 'k -> real) (normE : 'e -> real) <=>
      (!x. smul oneK x = x) /\
      (!a b x. smul (mulK a b) x = smul a (smul b x)) /\
      (!a b x. smul (addK a b) x = addE (smul a x) (smul b x)) /\
      (!a x y. smul a (addE x y) = addE (smul a x) (smul a y)) /\
      (!x. smul zeroK x = zeroE) /\
      (!a. smul a zeroE = zeroE) /\
      (!a x. normE (smul a x) = normK a * normE x)``);

val identity_pow_def = new_definition (
  "identity_pow_def",
  ``identity_pow (oneK : 'k) (mulK : 'k -> 'k -> 'k)
      (x : 'k) (n : num) =
      FOLDL mulK oneK (GENLIST (\i. x) n)``);

val identity_partial_sum_def = new_definition (
  "identity_partial_sum_def",
  ``identity_partial_sum
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (a : num -> 'e) (n : num) =
      FOLDL addE zeroE (GENLIST a n)``);

val identity_has_sum_def = new_definition (
  "identity_has_sum_def",
  ``identity_has_sum
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (normE : 'e -> real)
      (a : num -> 'e) (s : 'e) <=>
      !eps : real.
        0 < eps ==>
        ?N : num. !n : num.
          N <= n ==>
          normE
            (addE (identity_partial_sum zeroE addE a n) (negE s))
          < eps``);

val identity_analytic_at_def = new_definition (
  "identity_analytic_at_def",
  ``identity_analytic_at
      (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smul : 'k -> 'e -> 'e)
      (normK : 'k -> real) (normE : 'e -> real)
      (f : 'k -> 'e) (x : 'k) <=>
      ?a : num -> 'e. ?r : real.
        0 < r /\
        !y : 'k.
          normK y < r ==>
          identity_has_sum zeroE addE negE normE
            (\n. smul (identity_pow oneK mulK y n) (a n))
            (f (addK x y))``);

val identity_analytic_on_nhd_def = new_definition (
  "identity_analytic_on_nhd_def",
  ``identity_analytic_on_nhd
      (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smul : 'k -> 'e -> 'e)
      (normK : 'k -> real) (normE : 'e -> real)
      (f : 'k -> 'e) (U : 'k -> bool) <=>
      !x : 'k.
        U x ==>
        identity_analytic_at oneK addK mulK zeroE addE negE
          smul normK normE f x``);

val identity_open_def = new_definition (
  "identity_open_def",
  ``identity_open
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) (s : 'k -> bool) <=>
      !x : 'k.
        s x ==>
        ?r : real.
          0 < r /\
          !y : 'k.
            normK (addK (negK x) y) < r ==> s y``);

val identity_preconnected_def = new_definition (
  "identity_preconnected_def",
  ``identity_preconnected
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real) (U : 'k -> bool) <=>
      !u v : 'k -> bool.
        identity_open addK negK normK u /\
        identity_open addK negK normK v /\
        (!x. U x ==> u x \/ v x) /\
        (?x. U x /\ u x) /\
        (?x. U x /\ v x)
        ==>
        ?x. U x /\ u x /\ v x``);

val identity_frequently_eq_punctured_def = new_definition (
  "identity_frequently_eq_punctured_def",
  ``identity_frequently_eq_punctured
      (addK : 'k -> 'k -> 'k) (negK : 'k -> 'k)
      (normK : 'k -> real)
      (f : 'k -> 'e) (g : 'k -> 'e) (z0 : 'k) <=>
      !eps : real.
        0 < eps ==>
        ?z : 'k.
          z <> z0 /\
          normK (addK (negK z0) z) < eps /\
          f z = g z``);

val AnalyticOnNhd_eqOn_of_preconnected_of_frequently_eq =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (normE : 'e -> real)
      (smul : 'k -> 'e -> 'e)
      (U : 'k -> bool) (f : 'k -> 'e) (g : 'k -> 'e)
      (z0 : 'k).
      identity_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      identity_normed_add_comm_group zeroE addE negE normE /\
      identity_normed_space
        zeroK oneK addK mulK zeroE addE smul normK normE /\
      identity_analytic_on_nhd
        oneK addK mulK zeroE addE negE smul normK normE f U /\
      identity_analytic_on_nhd
        oneK addK mulK zeroE addE negE smul normK normE g U /\
      identity_preconnected addK negK normK U /\
      U z0 /\
      identity_frequently_eq_punctured addK negK normK f g z0
      ==>
      !z : 'k. U z ==> f z = g z``;
