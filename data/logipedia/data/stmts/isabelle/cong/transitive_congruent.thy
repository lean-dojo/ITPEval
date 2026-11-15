(*
  Statement-only formalization of Logipedia corpus artifact
  cong.transitive_congruent, catalog title cong.transitive_congruent:
  congruence of natural numbers modulo any natural modulus is a transitive
  relation. This file contains no proof.
*)

theory transitive_congruent
  imports Main
begin

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem transitive_congruent:
  fixes p :: nat
  shows "\<forall>x y z.
    congruent x y p \<longrightarrow>
    congruent y z p \<longrightarrow>
    congruent x z p"
  sorry

end
