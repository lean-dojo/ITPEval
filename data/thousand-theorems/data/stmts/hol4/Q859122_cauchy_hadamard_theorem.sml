(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q859122 (thousand-theorems__hol4__Q859122), "Cauchy–Hadamard theorem":
  for a formal multilinear series over an arbitrary nontrivially normed
  field, the inverse convergence radius is the limsup of the nth roots of
  its coefficient operator norms. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory transcTheory;
open extrealTheory;

val q859122_nontrivially_normed_field_def = new_definition (
  "q859122_nontrivially_normed_field_def",
  ``q859122_nontrivially_normed_field
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real) <=>
      zeroK <> oneK /\
      (!a b. addK a b = addK b a) /\
      (!a b c. addK (addK a b) c = addK a (addK b c)) /\
      (!a. addK zeroK a = a) /\
      (!a. addK (negK a) a = zeroK) /\
      (!a b. mulK a b = mulK b a) /\
      (!a b c. mulK (mulK a b) c = mulK a (mulK b c)) /\
      (!a. mulK oneK a = a) /\
      (!a b c. mulK a (addK b c) =
                 addK (mulK a b) (mulK a c)) /\
      invK zeroK = zeroK /\
      (!a. a <> zeroK ==> mulK (invK a) a = oneK) /\
      (!a. 0 <= normK a) /\
      (!a. (normK a = 0) <=> (a = zeroK)) /\
      normK oneK = 1 /\
      (!a. normK (negK a) = normK a) /\
      (!a b. normK (addK a b) <= normK a + normK b) /\
      (!a b. normK (mulK a b) = normK a * normK b) /\
      ?a. 1 < normK a``);

val q859122_normed_space_def = new_definition (
  "q859122_normed_space_def",
  ``q859122_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (normV : 'v -> real) <=>
      (!x y. addV x y = addV y x) /\
      (!x y z. addV (addV x y) z = addV x (addV y z)) /\
      (!x. addV zeroV x = x) /\
      (!x. addV (negV x) x = zeroV) /\
      (!x. smulV oneK x = x) /\
      (!a b x. smulV (mulK a b) x = smulV a (smulV b x)) /\
      (!a b x. smulV (addK a b) x =
                 addV (smulV a x) (smulV b x)) /\
      (!a x y. smulV a (addV x y) =
                 addV (smulV a x) (smulV a y)) /\
      (!x. smulV zeroK x = zeroV) /\
      (!a. smulV a zeroV = zeroV) /\
      (!x. 0 <= normV x) /\
      (!x. (normV x = 0) <=> (x = zeroV)) /\
      (!x. normV (negV x) = normV x) /\
      (!x y. normV (addV x y) <= normV x + normV y) /\
      (!a x. normV (smulV a x) = normK a * normV x)``);

val q859122_list_norm_product_def = new_definition (
  "q859122_list_norm_product_def",
  ``q859122_list_norm_product (normV : 'v -> real) (xs : 'v list) =
      FOLDL (\acc x. acc * normV x) 1 xs``);

val q859122_formal_multilinear_series_def = new_definition (
  "q859122_formal_multilinear_series_def",
  ``q859122_formal_multilinear_series
      (addK : 'k -> 'k -> 'k)
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (addF : 'f -> 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normE : 'e -> real) (normF : 'f -> real)
      (p : num -> 'e list -> 'f) (opnorm : num -> real) <=>
      (!n i xs x y.
        LENGTH xs = n /\ i < n ==>
        p n (LUPDATE (addE x y) i xs) =
          addF
            (p n (LUPDATE x i xs))
            (p n (LUPDATE y i xs))) /\
      (!n i xs a x.
        LENGTH xs = n /\ i < n ==>
        p n (LUPDATE (smulE a x) i xs) =
          smulF a (p n (LUPDATE x i xs))) /\
      !n.
        0 <= opnorm n /\
        (!xs.
          LENGTH xs = n ==>
          normF (p n xs) <=
            opnorm n * q859122_list_norm_product normE xs) /\
        !C : real.
          0 <= C /\
          (!xs.
            LENGTH xs = n ==>
            normF (p n xs) <=
              C * q859122_list_norm_product normE xs)
          ==>
          opnorm n <= C``);

val q859122_radius_def = new_definition (
  "q859122_radius_def",
  ``q859122_radius (opnorm : num -> real) =
      sup
        {Normal r |
          0 <= r /\
          ?C : real.
            !n.
              opnorm n * r pow n <= C}``);

val q859122_ennreal_inv_def = new_definition (
  "q859122_ennreal_inv_def",
  ``q859122_ennreal_inv (x : extreal) =
      if x = Normal 0 then PosInf else inv x``);

val q859122_nth_root_norm_def = new_definition (
  "q859122_nth_root_norm_def",
  ``q859122_nth_root_norm (opnorm : num -> real) (n : num) =
      Normal (opnorm n rpow (1 / &n))``);

val cauchy_hadamard_theorem =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (p : num -> 'e list -> 'f) (opnorm : num -> real).
      q859122_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q859122_normed_space
        zeroK oneK addK mulK normK
        zeroE addE negE smulE normE /\
      q859122_normed_space
        zeroK oneK addK mulK normK
        zeroF addF negF smulF normF /\
      q859122_formal_multilinear_series
        addK addE smulE addF smulF normE normF p opnorm
      ==>
      q859122_ennreal_inv (q859122_radius opnorm) =
      limsup (q859122_nth_root_norm opnorm)``;
