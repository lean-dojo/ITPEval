(*
  Statement-only formalization of the thousand-theorems corpus artifact Q765987,
  "Heine–Cantor theorem": every continuous map from a compact uniform space
  into a uniform space is uniformly continuous. This file contains no proof.
*)

theory Q765987_heine_cantor_theorem
  imports "HOL.Topological_Spaces"
begin

theorem heine_cantor_theorem:
  fixes f :: "'a::uniform_space \<Rightarrow> 'b::uniform_space"
  assumes compact_domain: "compact (UNIV :: 'a set)"
    and continuous_f: "continuous_on UNIV f"
  shows "uniformly_continuous_on UNIV f"
  sorry

end
