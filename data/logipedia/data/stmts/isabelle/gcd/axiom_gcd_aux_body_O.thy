(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_O, catalog title "gcd.axiom_gcd_aux_body_O": the
  source equality predicate relates the abstract auxiliary gcd body at zero
  to the curried function that returns its first natural-number argument.
  This file contains no proof.
*)

theory axiom_gcd_aux_body_O
  imports Main
begin

consts
  logipedia_connectives_equal :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  gcd_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem axiom_gcd_aux_body_O:
  "logipedia_connectives_equal
    (gcd_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)
    (\<lambda>m :: nat. \<lambda>n :: nat. m)"
  sorry

end
