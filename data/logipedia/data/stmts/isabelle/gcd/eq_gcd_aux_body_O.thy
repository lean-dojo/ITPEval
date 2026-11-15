(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_gcd_aux_body_O, catalog title "gcd.eq_gcd_aux_body_O": the abstract
  auxiliary gcd body at zero is Leibniz-equal to the curried function that
  returns its first natural-number argument. This file contains no proof.
*)

theory eq_gcd_aux_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  gcd_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_gcd_aux_body_O:
  "logipedia_leibniz
    (gcd_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)
    (\<lambda>m :: nat. \<lambda>n :: nat. m)"
  sorry

end
