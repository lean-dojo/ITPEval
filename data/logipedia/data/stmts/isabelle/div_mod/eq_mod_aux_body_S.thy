(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.eq_mod_aux_body_S, catalog title "div_mod.eq_mod_aux_body_S":
  at a successor index, the abstract auxiliary remainder body is
  Leibniz-equal to the curried natural-number function that returns the
  dividend when it is at most the divisor and otherwise recursively computes
  the auxiliary remainder. This file contains no proof.
*)

theory eq_mod_aux_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  mod_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_mod_aux_body_S:
  "\<forall>p :: nat.
    logipedia_leibniz
      (mod_aux_body (Suc p) :: nat \<Rightarrow> nat \<Rightarrow> nat)
      (\<lambda>m n.
        if m \<le> n
        then m
        else mod_aux p (m - Suc n) n)"
  sorry

end
