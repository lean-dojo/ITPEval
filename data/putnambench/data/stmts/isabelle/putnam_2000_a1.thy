theory putnam_2000_a1 imports
Complex_Main
begin

definition putnam_2000_a1_solution :: "real \<Rightarrow> real set" where
  "putnam_2000_a1_solution \<equiv> (\<lambda>A. {0<..<A^2})"
(* \<lambda> A. {0 <..< A ^ 2} *)
theorem putnam_2000_a1:
  fixes A :: real
  assumes Apos: "A > 0"
  shows "{S :: real. \<exists>x :: nat \<Rightarrow> real. (\<forall>j. x j > 0) \<and>
    x sums A \<and> (\<lambda>j. (x j)^2) sums S} = putnam_2000_a1_solution A"
  sorry

end
