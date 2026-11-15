(*
  Statement-only formalization of Lagrange's theorem from Hundred Theorems
  item 071. It states that the order of a subgroup divides the order of a
  finite group. This file contains no proof.
*)

theory Lagranges_Theorem
  imports "HOL-Algebra.Coset"
begin

theorem hundred_theorems_lagrange:
  fixes G :: "('a, 'b) monoid_scheme"
    and H :: "'a set"
  assumes "group G"
    and "subgroup H G"
    and "finite (carrier G)"
  shows "card H dvd order G"
  sorry

end
