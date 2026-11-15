(*
  Statement-only formalization of Logipedia corpus artifact div_mod.eq_div_O,
  catalog title div_mod.eq_div_O: if one natural number is strictly less than
  another, the source's total natural-number division gives quotient zero.
  This file contains no proof.
*)

theory eq_div_O
  imports Main
begin

primrec div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "div_aux 0 n m = 0"
| "div_aux (Suc p) n m =
    (if n \<le> m then 0 else Suc (div_aux p (n - Suc m) m))"

definition logipedia_div :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_div n m =
    (case m of 0 \<Rightarrow> Suc n | Suc p \<Rightarrow> div_aux n n p)"

theorem eq_div_O:
  fixes n m :: nat
  assumes "n < m"
  shows "logipedia_div n m = 0"
  sorry

end
