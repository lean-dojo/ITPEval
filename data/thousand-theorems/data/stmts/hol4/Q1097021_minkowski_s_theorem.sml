(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1097021 (thousand-theorems__hol4__Q1097021), "Minkowski's theorem": in a
  finite-dimensional real normed vector space with an additive Haar measure,
  a symmetric convex set whose measure exceeds 2^dim times the measure of a
  fundamental domain of a countable additive subgroup contains a nonzero
  subgroup point. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory extrealTheory;
open sigma_algebraTheory measureTheory;

val q1097021_real_normed_space_def = new_definition (
  "q1097021_real_normed_space_def",
  ``q1097021_real_normed_space
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real) <=>
      (!x y z. add x (add y z) = add (add x y) z) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x) /\
      (!x. add (neg x) x = zero) /\
      (!x. smul 1 x = x) /\
      (!a b x. smul (a * b) x = smul a (smul b x)) /\
      (!a b x. smul (a + b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. 0 <= norm x) /\
      (!x. norm x = 0 <=> x = zero) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q1097021_lincomb_def = new_definition (
  "q1097021_lincomb_def",
  ``q1097021_lincomb
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (basis : 'e list) (coeff : num -> real) =
      FOLDL
        (\acc i. add acc (smul (coeff i) (EL i basis)))
        zero
        (GENLIST (\i. i) (LENGTH basis))``);

val q1097021_basis_def = new_definition (
  "q1097021_basis_def",
  ``q1097021_basis
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (basis : 'e list) <=>
      ALL_DISTINCT basis /\
      (!coeff : num -> real.
        q1097021_lincomb zero add smul basis coeff = zero ==>
        !i. i < LENGTH basis ==> coeff i = 0) /\
      (!x : 'e.
        ?coeff : num -> real.
          q1097021_lincomb zero add smul basis coeff = x)``);

val q1097021_finite_dimensional_def = new_definition (
  "q1097021_finite_dimensional_def",
  ``q1097021_finite_dimensional
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e) <=>
      ?basis : 'e list. q1097021_basis zero add smul basis``);

val q1097021_dimension_def = new_definition (
  "q1097021_dimension_def",
  ``q1097021_dimension
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e) =
      LENGTH
        (@basis : 'e list. q1097021_basis zero add smul basis)``);

val q1097021_open_def = new_definition (
  "q1097021_open_def",
  ``q1097021_open
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : 'e set) <=>
      !x. x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. norm (add y (neg x)) < epsilon ==> y IN u``);

val q1097021_compact_def = new_definition (
  "q1097021_compact_def",
  ``q1097021_compact
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (k : 'e set) <=>
      !u : num -> 'e.
        (!n. u n IN k) ==>
        ?r : num -> num. ?x : 'e.
          x IN k /\
          (!p q. p < q ==> r p < r q) /\
          !epsilon : real.
            0 < epsilon ==>
            ?N : num. !n : num.
              N <= n ==>
              norm (add (u (r n)) (neg x)) < epsilon``);

val q1097021_borel_measure_def = new_definition (
  "q1097021_borel_measure_def",
  ``q1097021_borel_measure
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (m : 'e m_space) <=>
      measure_space m /\
      m_space m = UNIV /\
      measurable_sets m =
        subsets
          (sigma UNIV
            {u : 'e set | q1097021_open add neg norm u})``);

val q1097021_translate_def = new_definition (
  "q1097021_translate_def",
  ``q1097021_translate
      (add : 'e -> 'e -> 'e) (a : 'e) (s : 'e set) =
      {x | ?y. y IN s /\ x = add a y}``);

val q1097021_outer_measure_def = new_definition (
  "q1097021_outer_measure_def",
  ``q1097021_outer_measure (m : 'e m_space) (s : 'e set) =
      inf
        {r : extreal |
          ?t : 'e set.
            s SUBSET t /\
            t IN measurable_sets m /\
            measure m t = r}``);

val q1097021_add_haar_measure_def = new_definition (
  "q1097021_add_haar_measure_def",
  ``q1097021_add_haar_measure
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (m : 'e m_space) <=>
      (!a : 'e. !s : 'e set.
        q1097021_outer_measure m (q1097021_translate add a s) =
        q1097021_outer_measure m s) /\
      (!k : 'e set.
        q1097021_compact add neg norm k ==>
        q1097021_outer_measure m k <> PosInf) /\
      (!u : 'e set.
        q1097021_open add neg norm u /\ u <> {} ==>
        q1097021_outer_measure m u <> 0)``);

val q1097021_add_subgroup_def = new_definition (
  "q1097021_add_subgroup_def",
  ``q1097021_add_subgroup
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (lattice : 'e set) <=>
      zero IN lattice /\
      (!x y. x IN lattice /\ y IN lattice ==> add x y IN lattice) /\
      (!x. x IN lattice ==> neg x IN lattice)``);

val q1097021_add_fundamental_domain_def = new_definition (
  "q1097021_add_fundamental_domain_def",
  ``q1097021_add_fundamental_domain
      (add : 'e -> 'e -> 'e) (m : 'e m_space)
      (lattice : 'e set) (fund : 'e set) <=>
      fund IN subsets (completion m) /\
      q1097021_outer_measure m
        {x | ~(?a. a IN lattice /\ add a x IN fund)} = 0 /\
      (!a b.
        a IN lattice /\ b IN lattice /\ a <> b ==>
        q1097021_outer_measure m
          (q1097021_translate add a fund INTER
           q1097021_translate add b fund) = 0)``);

val q1097021_symmetric_def = new_definition (
  "q1097021_symmetric_def",
  ``q1097021_symmetric (neg : 'e -> 'e) (s : 'e set) <=>
      !x. x IN s ==> neg x IN s``);

val q1097021_convex_def = new_definition (
  "q1097021_convex_def",
  ``q1097021_convex
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (s : 'e set) <=>
      !x y t.
        x IN s /\ y IN s /\ 0 <= t /\ t <= 1 ==>
        add (smul (1 - t) x) (smul t y) IN s``);

val exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (m : 'e m_space) (lattice : 'e set)
      (fund : 'e set) (s : 'e set).
      q1097021_real_normed_space zero add neg smul norm /\
      q1097021_finite_dimensional zero add smul /\
      q1097021_borel_measure add neg norm m /\
      q1097021_add_haar_measure add neg norm m /\
      q1097021_add_subgroup zero add neg lattice /\
      COUNTABLE lattice /\
      q1097021_add_fundamental_domain add m lattice fund /\
      q1097021_symmetric neg s /\
      q1097021_convex add smul s /\
      q1097021_outer_measure m fund *
        Normal
          ((2 : real) pow q1097021_dimension zero add smul) <
        q1097021_outer_measure m s
      ==>
      ?x : 'e. x IN lattice /\ x <> zero /\ x IN s``;
