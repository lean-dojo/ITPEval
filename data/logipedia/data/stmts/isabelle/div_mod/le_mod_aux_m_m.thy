(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.le_mod_aux_m_m, catalog title "div_mod.le_mod_aux_m_m": whenever a
  natural dividend is at most the fuel index, the fuel-indexed auxiliary
  remainder is at most the natural divisor. This file contains no proof.
*)

theory le_mod_aux_m_m
  imports Main
begin

primrec mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "mod_aux 0 n m = n"
| "mod_aux (Suc p) n m =
    (if n \<le> m then n else mod_aux p (n - Suc m) m)"

theorem le_mod_aux_m_m:
  "\<forall>p n m :: nat. n \<le> p \<longrightarrow> mod_aux p n m \<le> m"
  sorry

end
