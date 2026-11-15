(*
  Statement-only formalization of Logipedia corpus artifact div_mod.mod_O_n,
  catalog title div_mod.mod_O_n: for every natural divisor, the source's total
  natural-number remainder operation maps zero to zero. This file contains no
  proof.
*)

theory mod_O_n
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

theorem mod_O_n:
  fixes n :: nat
  shows "logipedia_mod 0 n = 0"
  sorry

end
