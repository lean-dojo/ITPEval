(*
  Statement-only formalization of "De Moivre's Theorem" from Hundred Theorems item 017. This
  file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory complexTheory;

val de_moivre_s_theorem =
  ``!z : complex. !n : num.
      let ccos =
        \w : complex.
          (complex_exp (i * w) + complex_exp (-i * w)) / 2
      in
      let csin =
        \w : complex.
          (complex_exp (i * w) - complex_exp (-i * w)) / (2 * i)
      in
        (ccos z + i * csin z) pow n =
        ccos (complex_of_real (&n) * z) +
          i * csin (complex_of_real (&n) * z)``;
