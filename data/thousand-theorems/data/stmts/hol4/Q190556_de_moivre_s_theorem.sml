(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q190556, "De Moivre's theorem": for every natural number n and complex z,
  the nth power of cos z plus sin z times the imaginary unit equals the same
  cosine-sine expression at the complex-scaled argument n * z. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory complexTheory;

val de_moivre_s_theorem =
  ``!n : num. !z : complex.
      let ccos =
        \w : complex.
          (complex_exp (w * i) + complex_exp (-w * i)) / 2
      in
      let csin =
        \w : complex.
          (complex_exp (-w * i) - complex_exp (w * i)) * i / 2
      in
        (ccos z + csin z * i) pow n =
        ccos (complex_of_real (&n) * z) +
          csin (complex_of_real (&n) * z) * i``;
