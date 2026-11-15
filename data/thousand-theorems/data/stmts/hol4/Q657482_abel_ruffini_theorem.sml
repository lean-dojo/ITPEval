(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q657482, "Abel–Ruffini theorem": there exists a complex number algebraic
  over the rationals that is not solvable by radicals over the rationals.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory complexTheory pred_setTheory ratTheory realTheory
     real_of_ratTheory;

val q657482_exists_not_solvable_by_rad =
  ``let rational_complex =
      \q : rat. complex_of_real (real_of_rat q)
    in
    let algebraic_over_rationals =
      \x : complex.
        ?p : num -> rat.
          FINITE {n | p n <> 0} /\
          (?n. p n <> 0) /\
          ITSET
            (\n z. rational_complex (p n) * x pow n + z)
            {n | p n <> 0} 0 = 0
    in
    let solvable_by_radicals =
      \x : complex.
        !S : complex -> bool.
          ((!q : rat. S (rational_complex q)) /\
           (!u v : complex.
              S u /\ S v ==> S (u + v) /\ S (u * v)) /\
           (!u : complex.
              S u ==> S (0 - u)) /\
           (!u : complex.
              S u ==> S (1 / u)) /\
           (!n : num. !u : complex.
              0 < n /\ S (u pow n) ==> S u))
          ==> S x
    in
      ?x : complex.
        algebraic_over_rationals x /\
        ~solvable_by_radicals x``;
