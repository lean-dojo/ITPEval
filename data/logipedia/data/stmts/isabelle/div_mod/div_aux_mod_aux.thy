(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.div_aux_mod_aux, catalog title "div_mod.div_aux_mod_aux": the
  fuel-indexed auxiliary quotient and remainder functions decompose every
  natural dividend as quotient times one plus the divisor, plus the
  remainder. This file contains no proof.
*)

theory div_aux_mod_aux
  imports Main
begin

primrec mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mod_aux 0 n m = n"
| "mod_aux (Suc p) n m =
    (if n \<le> m then n else mod_aux p (n - Suc m) m)"

primrec div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "div_aux 0 n m = 0"
| "div_aux (Suc p) n m =
    (if n \<le> m then 0 else Suc (div_aux p (n - Suc m) m))"

theorem div_aux_mod_aux:
  "\<forall>p n m :: nat.
    n = div_aux p n m * Suc m + mod_aux p n m"
  sorry

end
