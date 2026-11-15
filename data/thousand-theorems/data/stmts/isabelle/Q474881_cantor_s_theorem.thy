(*
  Statement-only formalization of thousand-theorems corpus artifact Q474881,
  "Cantor's theorem": no function from an arbitrary type onto its full set of
  subsets is surjective. This file contains no proof.
*)

theory Q474881_cantor_s_theorem
  imports Main
begin

theorem cantor_s_theorem:
  fixes f :: "'a \<Rightarrow> 'a set"
  shows "\<not> surj f"
  sorry

end
