(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527189
  (thousand-theorems__isabelle__Q3527189), "Lattice theorem": Noether's third
  isomorphism theorem identifies (G/N)/(M/N) canonically with G/M for normal
  subgroups N contained in M. This file contains no proof.
*)

theory Q3527189_lattice_theorem
  imports "HOL-Algebra.Coset"
begin

definition q3527189_factor_subgroup ::
    "('a, 'b) monoid_scheme \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set"
  where
    "q3527189_factor_subgroup G N M =
      rcosets\<^bsub>G\<lparr>carrier := M\<rparr>\<^esub> N"

definition q3527189_canonical_map :: "'a set set \<Rightarrow> 'a set"
  where
    "q3527189_canonical_map X = \<Union>X"

theorem q3527189_quotient_quotient_equiv_quotient:
  fixes G :: "('a, 'b) monoid_scheme"
    and N M :: "'a set"
  assumes group_G: "group G"
    and normal_N: "N \<lhd> G"
    and normal_M: "M \<lhd> G"
    and nested: "N \<subseteq> M"
  shows "q3527189_canonical_map \<in>
      iso ((G Mod N) Mod (q3527189_factor_subgroup G N M)) (G Mod M) \<and>
    (\<forall>g \<in> carrier G.
      q3527189_canonical_map
        (r_coset (G Mod N) (q3527189_factor_subgroup G N M)
          (r_coset G N g)) =
      r_coset G M g)"
  oops

end
