(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1306095, "Whitney embedding theorem": every compact Hausdorff smooth
  finite-dimensional real manifold admits a smooth closed embedding into
  some finite-dimensional Euclidean space, with injective derivative
  everywhere. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pred_setTheory realTheory transcTheory;
open topologyTheory;

val q1306095_real_normed_space_def = new_definition (
  "q1306095_real_normed_space_def",
  ``q1306095_real_normed_space
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
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y) /\
      (!a x. norm (smul a x) = abs a * norm x)``);

val q1306095_lincomb_def = new_definition (
  "q1306095_lincomb_def",
  ``q1306095_lincomb
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (basis : 'e list) (coeff : num -> real) =
      FOLDL
        (\acc i. add acc (smul (coeff i) (EL i basis)))
        zero
        (GENLIST (\i. i) (LENGTH basis))``);

val q1306095_basis_def = new_definition (
  "q1306095_basis_def",
  ``q1306095_basis
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (basis : 'e list) <=>
      (!coeff : num -> real.
        q1306095_lincomb zero add smul basis coeff = zero
        ==>
        !i. i < LENGTH basis ==> coeff i = 0) /\
      (!x : 'e.
        ?coeff : num -> real.
          q1306095_lincomb zero add smul basis coeff = x)``);

val q1306095_finite_dimensional_def = new_definition (
  "q1306095_finite_dimensional_def",
  ``q1306095_finite_dimensional
      (zero : 'e) (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e) <=>
      ?basis : 'e list. q1306095_basis zero add smul basis``);

val q1306095_linear_def = new_definition (
  "q1306095_linear_def",
  ``q1306095_linear
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smulE : real -> 'e -> 'e)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (smulF : real -> 'f -> 'f) (L : 'e -> 'f) <=>
      L zeroE = zeroF /\
      (!x y. L (addE x y) = addF (L x) (L y)) /\
      (!a x. L (smulE a x) = smulF a (L x))``);

val q1306095_open_def = new_definition (
  "q1306095_open_def",
  ``q1306095_open
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : 'e set) <=>
      !x. x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y. norm (add y (neg x)) < epsilon ==> y IN u``);

val q1306095_has_derivative_within_def = new_definition (
  "q1306095_has_derivative_within_def",
  ``q1306095_has_derivative_within
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : real -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : real -> 'f -> 'f)
      (normF : 'f -> real)
      (s : 'e set) (f : 'e -> 'f) (x : 'e) (L : 'e -> 'f) <=>
      q1306095_linear zeroE addE smulE zeroF addF smulF L /\
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y.
            y IN s /\
            0 < normE (addE y (negE x)) /\
            normE (addE y (negE x)) < delta
            ==>
            normF
              (addF
                (addF (f y) (negF (f x)))
                (negF (L (addE y (negE x))))) <=
              epsilon * normE (addE y (negE x))``);

val q1306095_unique_diff_on_def = new_definition (
  "q1306095_unique_diff_on_def",
  ``q1306095_unique_diff_on
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (s : 'e set) <=>
      !x L.
        x IN s /\
        q1306095_linear zero add smul 0 $+ $* L /\
        (!epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              y IN s /\
              0 < norm (add y (neg x)) /\
              norm (add y (neg x)) < delta
              ==>
              abs (L (add y (neg x))) <=
                epsilon * norm (add y (neg x)))
        ==>
        !v. L v = 0``);

val q1306095_convex_def = new_definition (
  "q1306095_convex_def",
  ``q1306095_convex
      (add : 'e -> 'e -> 'e) (smul : real -> 'e -> 'e)
      (s : 'e set) <=>
      !x y t.
        x IN s /\ y IN s /\ 0 <= t /\ t <= 1
        ==>
        add (smul t x) (smul (1 - t) y) IN s``);

val q1306095_nonempty_interior_def = new_definition (
  "q1306095_nonempty_interior_def",
  ``q1306095_nonempty_interior
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (s : 'e set) <=>
      ?x epsilon.
        x IN s /\
        0 < epsilon /\
        !y. norm (add y (neg x)) < epsilon ==> y IN s``);

val q1306095_multilinear_def = new_definition (
  "q1306095_multilinear_def",
  ``q1306095_multilinear
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smulE : real -> 'e -> 'e)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (smulF : real -> 'f -> 'f)
      k (A : 'e list -> 'f) <=>
      !args i.
        LENGTH args = k /\ i < k
        ==>
        A (LUPDATE zeroE i args) = zeroF /\
        (!u v.
          A (LUPDATE (addE u v) i args) =
            addF
              (A (LUPDATE u i args))
              (A (LUPDATE v i args))) /\
        (!a u.
          A (LUPDATE (smulE a u) i args) =
            smulF a (A (LUPDATE u i args)))``);

val q1306095_has_smooth_jet_within_def = new_definition (
  "q1306095_has_smooth_jet_within_def",
  ``q1306095_has_smooth_jet_within
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : real -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : real -> 'f -> 'f)
      (normF : 'f -> real)
      (s : 'e set) (f : 'e -> 'f)
      (J : num -> 'e -> 'e list -> 'f) <=>
      (!x. x IN s ==> J 0 x [] = f x) /\
      (!k x.
        x IN s ==>
        q1306095_multilinear
          zeroE addE smulE zeroF addF smulF k (J k x)) /\
      (!k x args.
        x IN s /\ LENGTH args = k
        ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              y IN s /\
              0 < normE (addE y (negE x)) /\
              normE (addE y (negE x)) < delta
              ==>
              normF
                (addF
                  (addF (J k y args) (negF (J k x args)))
                  (negF
                    (J (SUC k) x
                      ((addE y (negE x))::args)))) <=
                epsilon *
                normE (addE y (negE x)) *
                FOLDL (\p r. p * r) 1 (MAP normE args))``);

val q1306095_smooth_on_def = new_definition (
  "q1306095_smooth_on_def",
  ``q1306095_smooth_on
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : real -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : real -> 'f -> 'f)
      (normF : 'f -> real)
      (s : 'e set) (f : 'e -> 'f) <=>
      ?J : num -> 'e -> 'e list -> 'f.
        q1306095_has_smooth_jet_within
          zeroE addE negE smulE normE
          zeroF addF negF smulF normF s f J``);

val q1306095_compact_def = new_definition (
  "q1306095_compact_def",
  ``q1306095_compact (top : 'm topology) (carrier : 'm set) <=>
      !cover : ('m set) set.
        (!u. u IN cover ==> open_in top u) /\
        carrier SUBSET UNIONS cover
        ==>
        ?subcover.
          FINITE subcover /\
          subcover SUBSET cover /\
          carrier SUBSET UNIONS subcover``);

val q1306095_hausdorff_def = new_definition (
  "q1306095_hausdorff_def",
  ``q1306095_hausdorff (top : 'm topology) (carrier : 'm set) <=>
      !x y.
        x IN carrier /\ y IN carrier /\ x <> y
        ==>
        ?u v.
          open_in top u /\ open_in top v /\
          x IN u /\ y IN v /\ DISJOINT u v``);

val q1306095_charted_manifold_def = new_definition (
  "q1306095_charted_manifold_def",
  ``q1306095_charted_manifold
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (corner : 'e set)
      (top : 'm topology) (carrier : 'm set)
      (charts : 'c set)
      (source : 'c -> 'm set) (target : 'c -> 'e set)
      (chart : 'c -> 'm -> 'e) (chart_inv : 'c -> 'e -> 'm) <=>
      topspace top = carrier /\
      q1306095_real_normed_space zero add neg smul norm /\
      q1306095_finite_dimensional zero add smul /\
      q1306095_convex add smul corner /\
      q1306095_nonempty_interior add neg norm corner /\
      q1306095_unique_diff_on zero add neg smul norm corner /\
      q1306095_compact top carrier /\
      q1306095_hausdorff top carrier /\
      (!c. c IN charts ==> open_in top (source c)) /\
      carrier = UNIONS (IMAGE source charts) /\
      (!c. c IN charts ==>
        source c SUBSET carrier /\
        (?u.
          q1306095_open add neg norm u /\
          target c = corner INTER u) /\
        (!x. x IN source c ==>
          chart c x IN target c /\ chart_inv c (chart c x) = x) /\
        (!z. z IN target c ==>
          chart_inv c z IN source c /\ chart c (chart_inv c z) = z) /\
        (!u.
          q1306095_open add neg norm u ==>
          open_in top
            {x | x IN source c /\ chart c x IN u}) /\
        (!u.
          open_in top u ==>
          ?v.
            q1306095_open add neg norm v /\
            {z | z IN target c /\ chart_inv c z IN u} =
              target c INTER v)) /\
      (!a b.
        a IN charts /\ b IN charts ==>
        q1306095_smooth_on
          zero add neg smul norm zero add neg smul norm
          {z | z IN target a /\ chart_inv a z IN source b}
          (\z. chart b (chart_inv a z)))``);

val q1306095_euclidean_active_def = new_definition (
  "q1306095_euclidean_active_def",
  ``q1306095_euclidean_active n (x : num -> real) <=>
      !i. n <= i ==> x i = 0``);

val q1306095_euclidean_norm_def = new_definition (
  "q1306095_euclidean_norm_def",
  ``q1306095_euclidean_norm n (x : num -> real) =
      sqrt (SIGMA (\i. x i * x i) (count n))``);

val q1306095_euclidean_open_def = new_definition (
  "q1306095_euclidean_open_def",
  ``q1306095_euclidean_open n (u : (num -> real) set) <=>
      u SUBSET {x | q1306095_euclidean_active n x} /\
      !x. x IN u ==>
        ?epsilon : real.
          0 < epsilon /\
          !y.
            q1306095_euclidean_active n y /\
            q1306095_euclidean_norm n (\i. y i - x i) < epsilon
            ==>
            y IN u``);

val q1306095_euclidean_closed_def = new_definition (
  "q1306095_euclidean_closed_def",
  ``q1306095_euclidean_closed n (s : (num -> real) set) <=>
      s SUBSET {x | q1306095_euclidean_active n x} /\
      q1306095_euclidean_open n
        ({x | q1306095_euclidean_active n x} DIFF s)``);

val q1306095_smooth_manifold_map_def = new_definition (
  "q1306095_smooth_manifold_map_def",
  ``q1306095_smooth_manifold_map
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (carrier : 'm set)
      (charts : 'c set) (target : 'c -> 'e set)
      (chart_inv : 'c -> 'e -> 'm)
      n (f : 'm -> num -> real) <=>
      (!x. x IN carrier ==> q1306095_euclidean_active n (f x)) /\
      !c. c IN charts ==>
        q1306095_smooth_on
          zero add neg smul norm
          (\i. 0) (\x y i. x i + y i) (\x i. -x i)
          (\a x i. a * x i) (q1306095_euclidean_norm n)
          (target c) (\z. f (chart_inv c z))``);

val q1306095_closed_embedding_def = new_definition (
  "q1306095_closed_embedding_def",
  ``q1306095_closed_embedding
      (top : 'm topology) (carrier : 'm set)
      n (f : 'm -> num -> real) <=>
      (!x. x IN carrier ==> q1306095_euclidean_active n (f x)) /\
      (!x y. x IN carrier /\ y IN carrier /\ f x = f y ==> x = y) /\
      (!u.
        q1306095_euclidean_open n u ==>
        open_in top {x | x IN carrier /\ f x IN u}) /\
      q1306095_euclidean_closed n (IMAGE f carrier)``);

val q1306095_injective_mfderiv_def = new_definition (
  "q1306095_injective_mfderiv_def",
  ``q1306095_injective_mfderiv
      (zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (carrier : 'm set) (charts : 'c set)
      (source : 'c -> 'm set) (target : 'c -> 'e set)
      (chart : 'c -> 'm -> 'e) (chart_inv : 'c -> 'e -> 'm)
      n (f : 'm -> num -> real) <=>
      !x.
        x IN carrier ==>
        ?c.
          c IN charts /\ x IN source c /\
          (?L.
            (!v. q1306095_euclidean_active n (L v)) /\
            q1306095_has_derivative_within
              zero add neg smul norm
              (\i. 0) (\u v i. u i + v i) (\u i. -u i)
              (\a u i. a * u i) (q1306095_euclidean_norm n)
              (target c) (\z. f (chart_inv c z)) (chart c x) L) /\
          (!L.
            (!v. q1306095_euclidean_active n (L v)) /\
            q1306095_has_derivative_within
              zero add neg smul norm
              (\i. 0) (\u v i. u i + v i) (\u i. -u i)
              (\a u i. a * u i) (q1306095_euclidean_norm n)
              (target c) (\z. f (chart_inv c z)) (chart c x) L
            ==>
            !u v. L u = L v ==> u = v)``);

val exists_embedding_euclidean_of_compact =
  ``!(zero : 'e) (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (smul : real -> 'e -> 'e) (norm : 'e -> real)
      (corner : 'e set)
      (top : 'm topology) (carrier : 'm set)
      (charts : 'c set)
      (source : 'c -> 'm set) (target : 'c -> 'e set)
      (chart : 'c -> 'm -> 'e) (chart_inv : 'c -> 'e -> 'm).
      q1306095_charted_manifold
        zero add neg smul norm corner top carrier
        charts source target chart chart_inv
      ==>
      ?n (f : 'm -> num -> real).
        q1306095_smooth_manifold_map
          zero add neg smul norm carrier charts target chart_inv n f /\
        q1306095_closed_embedding top carrier n f /\
        q1306095_injective_mfderiv
          zero add neg smul norm carrier charts source target chart chart_inv n f``;
