(*
  Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_l,
  catalog title "sigma_pi.exp_pi_l": multiplying a natural-number product by
  a power distributes one copy of the base into every factor.
  This file contains no proof.
*)

theory exp_pi_l
  imports Main
begin

theorem exp_pi_l:
  fixes n a :: nat
    and f :: "nat \<Rightarrow> nat"
  shows
    "a ^ n * (\<Prod>i < n. f i) =
      (\<Prod>i < n. a * f i)"
  sorry

end
