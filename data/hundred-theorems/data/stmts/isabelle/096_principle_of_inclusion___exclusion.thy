(*
  Statement-only formalization of Hundred Theorems artifact 096, "Principle of
  Inclusion / Exclusion". It states the alternating-sum formula for the
  cardinality of a finite union of finitely indexed finite sets. This file
  contains no proof.
*)

theory Principle_of_Inclusion_Exclusion
  imports Main
begin

theorem principle_of_inclusion_exclusion:
  fixes A :: "'i set"
    and X :: "'i \<Rightarrow> 'a set"
  assumes "finite A"
    and "\<And>i. i \<in> A \<Longrightarrow> finite (X i)"
  shows "int (card (\<Union>(X ` A))) =
    (\<Sum>B | B \<subseteq> A \<and> B \<noteq> {}.
      (-1) ^ (card B + 1) * int (card (\<Inter>(X ` B))))"
  sorry

end
