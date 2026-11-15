(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3527263 (thousand-theorems__isabelle__Q3527263), "Kleene fixed-point
  theorem": an omega-Scott-continuous endomap of a complete lattice has least
  fixed point equal to the supremum of its finite iterates from bottom. This
  file contains no proof.
*)

theory Q3527263_kleene_fixed_point_theorem
  imports Main
begin

definition q3527263_omega_scott_continuous ::
    "('a::complete_lattice \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q3527263_omega_scott_continuous f \<longleftrightarrow>
    mono f \<and>
    (\<forall>M::nat \<Rightarrow> 'a. mono M \<longrightarrow>
      f (SUP n. M n) = (SUP n. f (M n)))"

theorem q3527263_kleene_fixed_point_theorem:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes omega_scott_continuous: "q3527263_omega_scott_continuous f"
  shows "lfp f = (SUP n::nat. (f ^^ n) bot)"
  sorry

end
