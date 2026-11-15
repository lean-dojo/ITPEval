(*
  Statement-only formalization of Logipedia corpus artifact div_mod.div_times,
  catalog title div_mod.div_times: for natural numbers a and positive b, the
  source's total natural-number division sends a * b divided by b to a. This
  file contains no proof.
*)

theory div_times
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

theorem div_times:
  fixes a b :: nat
  assumes "0 < b"
  shows "logipedia_div (a * b) b = a"
  sorry

end
