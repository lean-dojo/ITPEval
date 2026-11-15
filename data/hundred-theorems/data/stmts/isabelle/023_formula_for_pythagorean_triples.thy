(*
  Statement-only formalization of Hundred Theorems artifact 023, "Formula for Pythagorean
  Triples": the integer solutions of x^2 + y^2 = z^2 are exactly the scaled Euclidean
  parametrizations, allowing either leg order and either sign for z. This file contains no proof.
*)

theory Formula_for_Pythagorean_Triples
  imports Main
begin

theorem formula_for_pythagorean_triples:
  fixes x y z :: int
  shows "x * x + y * y = z * z \<longleftrightarrow>
    (\<exists>k m n :: int.
      ((x = k * (m ^ 2 - n ^ 2) \<and> y = k * (2 * m * n)) \<or>
       (x = k * (2 * m * n) \<and> y = k * (m ^ 2 - n ^ 2))) \<and>
      (z = k * (m ^ 2 + n ^ 2) \<or> z = -k * (m ^ 2 + n ^ 2)))"
  sorry

end
