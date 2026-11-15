(*
  Statement-only formalization of "The Number of Subsets of a Set" from
  Hundred Theorems item 052. This file contains no proof.
*)

theory Number_Of_Subsets_Of_A_Set
  imports Main
begin

theorem number_of_subsets:
  fixes A :: "'a set"
  assumes "finite A"
  shows "card (Pow A) = 2 ^ card A"
  sorry

end
