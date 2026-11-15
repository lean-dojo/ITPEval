(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_mod,
  catalog title div_mod.div_mod: every pair of natural numbers satisfies the
  quotient-remainder decomposition for the source's total division and
  remainder operations, including its zero-divisor branches. This file
  contains no proof.
*)

theory div_mod
  imports Main
begin

primrec mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "mod_aux 0 n m = n"
| "mod_aux (Suc p) n m =
    (if n \<le> m then n else mod_aux p (n - Suc m) m)"

primrec div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "div_aux 0 n m = 0"
| "div_aux (Suc p) n m =
    (if n \<le> m then 0 else Suc (div_aux p (n - Suc m) m))"

definition logipedia_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_mod n m =
    (case m of 0 \<Rightarrow> n | Suc p \<Rightarrow> mod_aux n n p)"

definition logipedia_div :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_div n m =
    (case m of 0 \<Rightarrow> Suc n | Suc p \<Rightarrow> div_aux n n p)"

theorem div_mod:
  fixes n m :: nat
  shows "n = logipedia_div n m * m + logipedia_mod n m"
  sorry

end
