(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2021_a3:
  the positive integers whose corresponding sphere in real three-space has an
  inscribed regular tetrahedron with integer-coordinate vertices are exactly
  three times a positive square. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pairTheory realTheory intrealTheory
     transcTheory;

val putnam_2021_a3 =
  ``let coord =
      \P : real # (real # real).
      \i : num.
        if i = 0 then FST P
        else if i = 1 then FST (SND P)
        else SND (SND P)
    in
    let on_sphere =
      \N : num.
      \P : real # (real # real).
        (coord P 0) pow 2 +
        (coord P 1) pow 2 +
        (coord P 2) pow 2 = &N
    in
    let integer_coords =
      \P : real # (real # real).
        ?x y z : int.
          coord P 0 = real_of_int x /\
          coord P 1 = real_of_int y /\
          coord P 2 = real_of_int z
    in
    let dist =
      \P Q : real # (real # real).
        sqrt
          (((coord P 0 - coord Q 0) pow 2) +
           ((coord P 1 - coord Q 1) pow 2) +
           ((coord P 2 - coord Q 2) pow 2))
    in
    let has_integer_regular_tetrahedron =
      \N : num.
        ?A B C D : real # (real # real).
          on_sphere N A /\
          on_sphere N B /\
          on_sphere N C /\
          on_sphere N D /\
          integer_coords A /\
          integer_coords B /\
          integer_coords C /\
          integer_coords D /\
          ?s : real.
            0 < s /\
            dist A B = s /\
            dist A C = s /\
            dist A D = s /\
            dist B C = s /\
            dist B D = s /\
            dist C D = s
    in
    let solution =
      {n : num | ?m : num. 0 < m /\ n = 3 * m EXP 2}
    in
      !N : num.
        (0 < N /\ has_integer_regular_tetrahedron N) <=>
        N IN solution``;
