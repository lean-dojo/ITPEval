(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.let_clause_1078, catalog title "div_mod.let_clause_1078":
  under two natural-number quotient-remainder specifications and their
  explicit bounds, decompositions, and quotient comparisons, the first
  decomposition is restated with the addition and multiplication factors
  reversed. This file contains no proof.
*)

theory let_clause_1078
  imports Main
begin

definition div_mod_spec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "div_mod_spec n m q r \<longleftrightarrow> r < m \<and> n = q * m + r"

theorem let_clause_1078:
  fixes a b q r q1 r1 :: nat
  assumes "div_mod_spec a b q r"
    and "r < b"
    and "a = q * b + r"
    and "div_mod_spec a b q1 r1"
    and "r1 < b"
    and "a = q1 * b + r1"
    and "q \<le> q1"
    and "q < q1"
  shows "a = r + b * q"
  sorry

end
