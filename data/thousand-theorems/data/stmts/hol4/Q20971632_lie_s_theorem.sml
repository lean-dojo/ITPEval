(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q20971632, "Lie's theorem": a nonzero finite-dimensional triangularizable
  module over a solvable Lie algebra over a characteristic-zero field has a
  nonzero common weight vector for some linear functional. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory;

val q20971632_field_def = new_definition (
  "q20971632_field_def",
  ``q20971632_field
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k) <=>
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
      (!a. a <> zeroK ==> mulK (invK a) a = oneK)``);

val q20971632_nsmul_one_def = new_definition (
  "q20971632_nsmul_one_def",
  ``q20971632_nsmul_one
      (zeroK : 'k) (oneK : 'k) (addK : 'k -> 'k -> 'k) (n : num) =
      FUNPOW (addK oneK) n zeroK``);

val q20971632_char_zero_def = new_definition (
  "q20971632_char_zero_def",
  ``q20971632_char_zero
      (zeroK : 'k) (oneK : 'k) (addK : 'k -> 'k -> 'k) <=>
      !n. q20971632_nsmul_one zeroK oneK addK n = zeroK ==> n = 0``);

val q20971632_vector_space_def = new_definition (
  "q20971632_vector_space_def",
  ``q20971632_vector_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) <=>
      (!u v. addV u v = addV v u) /\
      (!u v w. addV (addV u v) w = addV u (addV v w)) /\
      (!v. addV zeroV v = v) /\
      (!v. addV (negV v) v = zeroV) /\
      (!v. smulV oneK v = v) /\
      (!a b v. smulV (mulK a b) v = smulV a (smulV b v)) /\
      (!a b v. smulV (addK a b) v =
                 addV (smulV a v) (smulV b v)) /\
      (!a u v. smulV a (addV u v) =
                 addV (smulV a u) (smulV a v)) /\
      (!v. smulV zeroK v = zeroV) /\
      (!a. smulV a zeroV = zeroV)``);

val q20971632_lie_algebra_def = new_definition (
  "q20971632_lie_algebra_def",
  ``q20971632_lie_algebra
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroL : 'l) (addL : 'l -> 'l -> 'l) (negL : 'l -> 'l)
      (smulL : 'k -> 'l -> 'l)
      (bracket : 'l -> 'l -> 'l) <=>
      q20971632_vector_space
        zeroK oneK addK mulK zeroL addL negL smulL /\
      (!x. bracket x x = zeroL) /\
      (!x y z. bracket (addL x y) z =
                 addL (bracket x z) (bracket y z)) /\
      (!x y z. bracket x (addL y z) =
                 addL (bracket x y) (bracket x z)) /\
      (!a x y. bracket (smulL a x) y = smulL a (bracket x y)) /\
      (!a x y. bracket x (smulL a y) = smulL a (bracket x y)) /\
      (!x y z.
        bracket x (bracket y z) =
        addL (bracket (bracket x y) z) (bracket y (bracket x z)))``);

val q20971632_lie_module_def = new_definition (
  "q20971632_lie_module_def",
  ``q20971632_lie_module
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroL : 'l) (addL : 'l -> 'l -> 'l)
      (smulL : 'k -> 'l -> 'l) (bracket : 'l -> 'l -> 'l)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (action : 'l -> 'v -> 'v) <=>
      q20971632_vector_space
        zeroK oneK addK mulK zeroV addV negV smulV /\
      (!x y v. action (addL x y) v =
                 addV (action x v) (action y v)) /\
      (!x u v. action x (addV u v) =
                 addV (action x u) (action x v)) /\
      (!a x v. action (smulL a x) v = smulV a (action x v)) /\
      (!a x v. action x (smulV a v) = smulV a (action x v)) /\
      (!x. action x zeroV = zeroV) /\
      (!v. action zeroL v = zeroV) /\
      (!x y v.
        action (bracket x y) v =
        addV (action x (action y v)) (negV (action y (action x v))))``);

val q20971632_subspace_def = new_definition (
  "q20971632_subspace_def",
  ``q20971632_subspace
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (U : 'v set) <=>
      zeroV IN U /\
      (!u v. u IN U /\ v IN U ==> addV u v IN U) /\
      (!v. v IN U ==> negV v IN U) /\
      (!a v. v IN U ==> smulV a v IN U)``);

val q20971632_span_def = new_definition (
  "q20971632_span_def",
  ``q20971632_span
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (s : 'v set) =
      {v |
        !U : 'v set.
          q20971632_subspace zeroV addV negV smulV U /\
          s SUBSET U
          ==>
          v IN U}``);

val q20971632_solvable_def = new_definition (
  "q20971632_solvable_def",
  ``q20971632_solvable
      (zeroL : 'l) (addL : 'l -> 'l -> 'l) (negL : 'l -> 'l)
      (smulL : 'k -> 'l -> 'l) (bracket : 'l -> 'l -> 'l) <=>
      ?D : num -> 'l set.
        D 0 = UNIV /\
        (!n.
          D (SUC n) =
          q20971632_span zeroL addL negL smulL
            {z | ?x y. x IN D n /\ y IN D n /\ z = bracket x y}) /\
        ?n. D n = {zeroL}``);

val q20971632_lincomb_def = new_definition (
  "q20971632_lincomb_def",
  ``q20971632_lincomb
      (zeroV : 'v) (addV : 'v -> 'v -> 'v)
      (smulV : 'k -> 'v -> 'v)
      (basis : 'v list) (coeff : num -> 'k) =
      FOLDL
        (\acc i. addV acc (smulV (coeff i) (EL i basis)))
        zeroV
        (GENLIST (\i. i) (LENGTH basis))``);

val q20971632_basis_def = new_definition (
  "q20971632_basis_def",
  ``q20971632_basis
      (zeroK : 'k)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (basis : 'v list) <=>
      (!coeff : num -> 'k.
        q20971632_lincomb zeroV addV smulV basis coeff = zeroV
        ==>
        !i. i < LENGTH basis ==> coeff i = zeroK) /\
      (!v : 'v.
        ?coeff : num -> 'k.
          q20971632_lincomb zeroV addV smulV basis coeff = v)``);

val q20971632_finite_dimensional_def = new_definition (
  "q20971632_finite_dimensional_def",
  ``q20971632_finite_dimensional
      (zeroK : 'k)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) <=>
      ?basis : 'v list.
        q20971632_basis zeroK zeroV addV smulV basis``);

val q20971632_triangularizable_def = new_definition (
  "q20971632_triangularizable_def",
  ``q20971632_triangularizable
      (zeroK : 'k)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (action : 'l -> 'v -> 'v) <=>
      !x : 'l.
        ?basis : 'v list.
          q20971632_basis zeroK zeroV addV smulV basis /\
          !j.
            j < LENGTH basis
            ==>
            ?coeff : num -> 'k.
              action x (EL j basis) =
                q20971632_lincomb zeroV addV smulV basis coeff /\
              !i. j < i /\ i < LENGTH basis ==> coeff i = zeroK``);

val q20971632_linear_functional_def = new_definition (
  "q20971632_linear_functional_def",
  ``q20971632_linear_functional
      (zeroK : 'k) (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (zeroL : 'l) (addL : 'l -> 'l -> 'l)
      (smulL : 'k -> 'l -> 'l) (chi : 'l -> 'k) <=>
      chi zeroL = zeroK /\
      (!x y. chi (addL x y) = addK (chi x) (chi y)) /\
      (!a x. chi (smulL a x) = mulK a (chi x))``);

val lie_s_theorem_statement =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (zeroL : 'l) (addL : 'l -> 'l -> 'l) (negL : 'l -> 'l)
      (smulL : 'k -> 'l -> 'l) (bracket : 'l -> 'l -> 'l)
      (zeroV : 'v) (addV : 'v -> 'v -> 'v) (negV : 'v -> 'v)
      (smulV : 'k -> 'v -> 'v) (action : 'l -> 'v -> 'v).
      q20971632_field zeroK oneK addK mulK negK invK /\
      q20971632_char_zero zeroK oneK addK /\
      q20971632_lie_algebra
        zeroK oneK addK mulK
        zeroL addL negL smulL bracket /\
      q20971632_lie_module
        zeroK oneK addK mulK
        zeroL addL smulL bracket
        zeroV addV negV smulV action /\
      q20971632_finite_dimensional zeroK zeroV addV smulV /\
      (?v : 'v. v <> zeroV) /\
      q20971632_solvable zeroL addL negL smulL bracket /\
      q20971632_triangularizable zeroK zeroV addV smulV action
      ==>
      ?chi : 'l -> 'k.
        q20971632_linear_functional
          zeroK addK mulK zeroL addL smulL chi /\
        ?v : 'v.
          v <> zeroV /\
          !x : 'l. action x v = smulV (chi x) v``;
