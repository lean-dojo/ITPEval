(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_div_aux_body_O, catalog title "div_mod.eq_div_aux_body_O":
  at index zero, the abstract auxiliary division body is Leibniz-equal to
  the constant-zero curried function on natural numbers. This file contains
  no proof.
*)

theory eq_div_aux_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_div_aux_body_O:
  "logipedia_leibniz
    (div_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)
    (\<lambda>m n. 0)"
  sorry

end
