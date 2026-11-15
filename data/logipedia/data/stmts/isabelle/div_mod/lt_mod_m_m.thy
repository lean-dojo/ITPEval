(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.lt_mod_m_m, catalog title div_mod.lt_mod_m_m: for every natural
  number and every positive natural modulus, the source's total remainder is
  strictly less than that modulus. This file contains no proof.
*)

theory lt_mod_m_m
  imports Main
begin

primrec mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "mod_aux 0 n m = n"
| "mod_aux (Suc p) n m =
    (if n \<le> m then n else mod_aux p (n - Suc m) m)"

definition logipedia_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_mod n m =
    (case m of 0 \<Rightarrow> n | Suc p \<Rightarrow> mod_aux n n p)"

theorem lt_mod_m_m:
  fixes n m :: nat
  assumes "0 < m"
  shows "logipedia_mod n m < m"
  sorry

end
