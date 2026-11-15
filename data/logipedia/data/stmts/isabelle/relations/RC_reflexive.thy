(*
  Statement-only formalization of Logipedia corpus artifact
  relations.RC_reflexive, catalog title "relations.RC_reflexive": the
  reflexive closure of an arbitrary binary relation is reflexive. This file
  contains no proof.
*)

theory RC_reflexive
  imports Main
begin

definition logipedia_reflexive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where
    "logipedia_reflexive R \<longleftrightarrow> (\<forall>x. R x x)"

definition logipedia_RC :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "logipedia_RC R x y \<longleftrightarrow> R x y \<or> x = y"

theorem RC_reflexive:
  "\<forall>R :: 'a \<Rightarrow> 'a \<Rightarrow> bool.
    logipedia_reflexive (logipedia_RC R)"
  sorry

end
