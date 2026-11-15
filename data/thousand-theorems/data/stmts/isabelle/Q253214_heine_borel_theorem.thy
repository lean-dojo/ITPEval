(*
  Statement-only formalization of thousand-theorems corpus artifact Q253214,
  "Heine–Borel theorem": in a proper metric space, a set is compact if and
  only if it is closed and bounded. This file contains no proof.
*)

theory Q253214_heine_borel_theorem
  imports "HOL-Analysis.Elementary_Metric_Spaces"
begin

theorem heine_borel_theorem:
  fixes S :: "'a::metric_space set"
  assumes proper: "\<And>x r. compact (cball x r)"
  shows "compact S \<longleftrightarrow> closed S \<and> bounded S"
  sorry

end
