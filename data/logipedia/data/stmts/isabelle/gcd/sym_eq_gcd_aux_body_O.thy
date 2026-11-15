(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_O, catalog title "gcd.sym_eq_gcd_aux_body_O": the
  curried function that returns its first natural-number argument is
  Leibniz-equal to the abstract auxiliary gcd body at zero. This file contains
  no proof.
*)

theory sym_eq_gcd_aux_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  gcd_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_gcd_aux_body_O:
  "logipedia_leibniz
    (\<lambda>m :: nat. \<lambda>n :: nat. m)
    (gcd_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
