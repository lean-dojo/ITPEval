(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q764287, "Van der Waerden's theorem": every finite coloring of an additive
  commutative monoid has a monochromatic positive-integer homothetic translate
  of each finite subset. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val q764287_add_comm_monoid_def = new_definition (
  "q764287_add_comm_monoid_def",
  ``q764287_add_comm_monoid
      (zero : 'm) (add : 'm -> 'm -> 'm) <=>
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x y. add x y = add y x) /\
      (!x. add zero x = x)``);

val q764287_nsmul_def = new_definition (
  "q764287_nsmul_def",
  ``q764287_nsmul
      (zero : 'm) (add : 'm -> 'm -> 'm) (n : num) (x : 'm) =
      FUNPOW (add x) n zero``);

val exists_mono_homothetic_copy =
  ``!(zero : 'm) (add : 'm -> 'm -> 'm)
      (S : 'm set) (C : 'm -> 'k).
      q764287_add_comm_monoid zero add /\
      FINITE S /\
      FINITE (UNIV : 'k set)
      ==>
      ?a : num.
        0 < a /\
        ?b : 'm. ?c : 'k.
          !s : 'm.
            s IN S
            ==>
            C (add (q764287_nsmul zero add a s) b) = c``;
