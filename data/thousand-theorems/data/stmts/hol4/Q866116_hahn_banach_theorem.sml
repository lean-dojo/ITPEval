(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q866116 (thousand-theorems__hol4__Q866116), "Hahn–Banach theorem": every
  continuous scalar-valued linear functional on a subspace of a seminormed
  space over a real-like normed field extends to the whole space with the
  same operator norm. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory realTheory complexTheory;

val q866116_nontrivially_normed_field_def = new_definition (
  "q866116_nontrivially_normed_field_def",
  ``q866116_nontrivially_normed_field
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

val q866116_real_field_isometry_def = new_definition (
  "q866116_real_field_isometry_def",
  ``q866116_real_field_isometry
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (toReal : 'k -> real) (fromReal : real -> 'k) <=>
      toReal zeroK = 0 /\
      toReal oneK = 1 /\
      (!a b. toReal (addK a b) = toReal a + toReal b) /\
      (!a b. toReal (mulK a b) = toReal a * toReal b) /\
      (!a. normK a = abs (toReal a)) /\
      (!a. fromReal (toReal a) = a) /\
      (!r. toReal (fromReal r) = r)``);

val q866116_complex_field_isometry_def = new_definition (
  "q866116_complex_field_isometry_def",
  ``q866116_complex_field_isometry
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (toComplex : 'k -> complex) (fromComplex : complex -> 'k) <=>
      toComplex zeroK = 0 /\
      toComplex oneK = 1 /\
      (!a b. toComplex (addK a b) = toComplex a + toComplex b) /\
      (!a b. toComplex (mulK a b) = toComplex a * toComplex b) /\
      (!a. normK a = modu (toComplex a)) /\
      (!a. fromComplex (toComplex a) = a) /\
      (!z. toComplex (fromComplex z) = z)``);

val q866116_is_rclike_normed_field_def = new_definition (
  "q866116_is_rclike_normed_field_def",
  ``q866116_is_rclike_normed_field
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real) <=>
      q866116_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      ((?toReal : 'k -> real. ?fromReal : real -> 'k.
          q866116_real_field_isometry
            zeroK oneK addK mulK normK toReal fromReal) \/
       (?toComplex : 'k -> complex. ?fromComplex : complex -> 'k.
          q866116_complex_field_isometry
            zeroK oneK addK mulK normK toComplex fromComplex))``);

val q866116_seminormed_add_comm_group_def = new_definition (
  "q866116_seminormed_add_comm_group_def",
  ``q866116_seminormed_add_comm_group
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (normE : 'e -> real) <=>
      (!x y z. addE (addE x y) z = addE x (addE y z)) /\
      (!x y. addE x y = addE y x) /\
      (!x. addE zeroE x = x) /\
      (!x. addE (negE x) x = zeroE) /\
      (!x. 0 <= normE x) /\
      normE zeroE = 0 /\
      (!x. normE (negE x) = normE x) /\
      (!x y. normE (addE x y) <= normE x + normE y)``);

val q866116_normed_space_def = new_definition (
  "q866116_normed_space_def",
  ``q866116_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smul : 'k -> 'e -> 'e) (normE : 'e -> real) <=>
      (!x. smul oneK x = x) /\
      (!a b x. smul (mulK a b) x = smul a (smul b x)) /\
      (!a b x.
        smul (addK a b) x = addE (smul a x) (smul b x)) /\
      (!a x y.
        smul a (addE x y) = addE (smul a x) (smul a y)) /\
      (!x. smul zeroK x = zeroE) /\
      (!a. smul a zeroE = zeroE) /\
      (!a x. normE (smul a x) = normK a * normE x)``);

val q866116_subspace_def = new_definition (
  "q866116_subspace_def",
  ``q866116_subspace
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smul : 'k -> 'e -> 'e) (p : 'e set) <=>
      zeroE IN p /\
      (!x y. x IN p /\ y IN p ==> addE x y IN p) /\
      (!a x. x IN p ==> smul a x IN p)``);

val q866116_continuous_linear_functional_on_def = new_definition (
  "q866116_continuous_linear_functional_on_def",
  ``q866116_continuous_linear_functional_on
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (addE : 'e -> 'e -> 'e) (smul : 'k -> 'e -> 'e)
      (normE : 'e -> real) (p : 'e set) (f : 'e -> 'k) <=>
      (!x y.
        x IN p /\ y IN p ==>
        f (addE x y) = addK (f x) (f y)) /\
      (!a x.
        x IN p ==>
        f (smul a x) = mulK a (f x)) /\
      ?C : real.
        0 <= C /\
        !x. x IN p ==> normK (f x) <= C * normE x``);

val q866116_is_operator_norm_on_def = new_definition (
  "q866116_is_operator_norm_on_def",
  ``q866116_is_operator_norm_on
      (normK : 'k -> real) (normE : 'e -> real)
      (p : 'e set) (f : 'e -> 'k) (n : real) <=>
      0 <= n /\
      (!x. x IN p ==> normK (f x) <= n * normE x) /\
      !C : real.
        0 <= C /\
        (!x. x IN p ==> normK (f x) <= C * normE x)
        ==>
        n <= C``);

val q866116_same_operator_norm_def = new_definition (
  "q866116_same_operator_norm_def",
  ``q866116_same_operator_norm
      (normK : 'k -> real) (normE : 'e -> real)
      (p : 'e set) (f : 'e -> 'k) (g : 'e -> 'k) <=>
      ?n : real.
        q866116_is_operator_norm_on normK normE p f n /\
        q866116_is_operator_norm_on normK normE UNIV g n``);

val exists_extension_norm_eq =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smul : 'k -> 'e -> 'e)
      (normE : 'e -> real) (p : 'e set) (f : 'e -> 'k).
      q866116_is_rclike_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q866116_seminormed_add_comm_group zeroE addE negE normE /\
      q866116_normed_space
        zeroK oneK addK mulK normK zeroE addE smul normE /\
      q866116_subspace zeroE addE smul p /\
      q866116_continuous_linear_functional_on
        addK mulK normK addE smul normE p f
      ==>
      ?g : 'e -> 'k.
        q866116_continuous_linear_functional_on
          addK mulK normK addE smul normE UNIV g /\
        (!x. x IN p ==> g x = f x) /\
        q866116_same_operator_norm normK normE p f g``;
