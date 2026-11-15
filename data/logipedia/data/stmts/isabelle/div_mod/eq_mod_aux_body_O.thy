(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_mod_aux_body_O, catalog title "div_mod.eq_mod_aux_body_O":
  at index zero, the abstract auxiliary remainder body is Leibniz-equal to
  the first-projection curried function on natural numbers. This file contains
  no proof.
*)

theory eq_mod_aux_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  mod_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_mod_aux_body_O:
  "logipedia_leibniz
    (mod_aux_body 0 :: nat \<Rightarrow> nat \<Rightarrow> nat)
    (\<lambda>m n. m)"
  sorry

end
