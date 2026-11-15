(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_div_aux_body_O, catalog title
  "div_mod.sym_eq_div_aux_body_O": at index zero, the constant-zero curried
  function on natural numbers is Leibniz-equal to the abstract auxiliary
  division body. This file contains no proof.
*)

theory sym_eq_div_aux_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_div_aux_body_O:
  "logipedia_leibniz
    (\<lambda>m n. 0)
    (div_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
