(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2023_a4:
  integer linear combinations of the twelve unit vertex vectors of a regular
  icosahedron are dense in real three-space. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory pred_setTheory realTheory;
open intrealTheory real_sigmaTheory transcTheory;

val putnam_2023_a4 =
  ``let zero3 = (0, (0, 0)) : real # (real # real)
    in
    let add3 =
      \x y : real # (real # real).
        (FST x + FST y,
         (FST (SND x) + FST (SND y),
          SND (SND x) + SND (SND y)))
    in
    let sub3 =
      \x y : real # (real # real).
        (FST x - FST y,
         (FST (SND x) - FST (SND y),
          SND (SND x) - SND (SND y)))
    in
    let smul3 =
      \c : real.
      \x : real # (real # real).
        (c * FST x, (c * FST (SND x), c * SND (SND x)))
    in
    let norm3 =
      \x : real # (real # real).
        sqrt
          (FST x pow 2 +
           FST (SND x) pow 2 +
           SND (SND x) pow 2)
    in
    let linear_isometry =
      \g : (real # (real # real)) -> (real # (real # real)).
        BIJ g UNIV UNIV /\
        (!x y : real # (real # real).
           g (add3 x y) = add3 (g x) (g y)) /\
        (!c : real.
           !x : real # (real # real).
             g (smul3 c x) = smul3 c (g x)) /\
        (!x : real # (real # real). norm3 (g x) = norm3 x)
    in
    let phi = (1 + sqrt 5) / 2
    in
    let scale = sqrt (1 + phi pow 2)
    in
    let vertex =
      \i : num.
        if i = 0 then (1, (phi, 0))
        else if i = 1 then (~1, (phi, 0))
        else if i = 2 then (1, (~phi, 0))
        else if i = 3 then (~1, (~phi, 0))
        else if i = 4 then (phi, (0, 1))
        else if i = 5 then (phi, (0, ~1))
        else if i = 6 then (~phi, (0, 1))
        else if i = 7 then (~phi, (0, ~1))
        else if i = 8 then (0, (1, phi))
        else if i = 9 then (0, (~1, phi))
        else if i = 10 then (0, (1, ~phi))
        else if i = 11 then (0, (~1, ~phi))
        else zero3
    in
    let is_icosahedron =
      \v : num -> real # (real # real).
        ?g : (real # (real # real)) -> (real # (real # real)).
          linear_isometry g /\
          !i : num.
            i < 12
            ==>
            g (v i) = smul3 (1 / scale) (vertex i)
    in
    let integer_combination =
      \v : num -> real # (real # real).
      \a : num -> int.
        (SIGMA
           (\i : num. real_of_int (a i) * FST (v i))
           (count 12),
         (SIGMA
            (\i : num. real_of_int (a i) * FST (SND (v i)))
            (count 12),
          SIGMA
            (\i : num. real_of_int (a i) * SND (SND (v i)))
            (count 12)))
    in
      !v : num -> real # (real # real).
      !w : real # (real # real).
      !epsilon : real.
        is_icosahedron v /\
        0 < epsilon
        ==>
        ?a : num -> int.
          norm3 (sub3 (integer_combination v a) w) < epsilon``;
