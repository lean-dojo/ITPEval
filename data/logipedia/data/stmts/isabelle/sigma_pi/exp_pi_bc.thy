(*
  Statement-only formalization of Logipedia corpus artifact sigma_pi.exp_pi_bc,
  catalog title "sigma_pi.exp_pi_bc": multiplying a shifted natural-number
  product by a power distributes one copy of the base into every factor.
  This file contains no proof.
*)

theory exp_pi_bc
  imports Main
begin

theorem exp_pi_bc:
  fixes a b c :: nat
    and f :: "nat \<Rightarrow> nat"
  shows
    "a ^ (c - b) * (\<Prod>i < c - b. f (i + b)) =
      (\<Prod>i < c - b. a * f (i + b))"
  sorry

end
