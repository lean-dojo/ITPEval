(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_mod_aux_body_S, catalog title
  "div_mod.sym_eq_mod_aux_body_S": at a successor index, the curried
  natural-number function that returns the dividend when it is at most the
  divisor and otherwise recursively computes the auxiliary remainder is
  Leibniz-equal to the abstract auxiliary remainder body. This file contains
  no proof.
*)

theory sym_eq_mod_aux_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  mod_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_mod_aux_body_S:
  "\<forall>p :: nat.
    logipedia_leibniz
      (\<lambda>m n.
        if m \<le> n
        then m
        else mod_aux p (m - Suc n) n)
      (mod_aux_body (Suc p) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
