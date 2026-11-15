(*
  Statement-only formalization of the thousand-theorems corpus artifact Q7208500
  (thousand-theorems__isabelle__Q7208500), "Poisson limit theorem": if the real
  sequence n * p n converges to r, then for each fixed natural k the associated
  binomial probability term converges to exp (-r) * r^k / k!. This file contains
  no proof.
*)

theory Q7208500_poisson_limit_theorem
  imports Complex_Main
begin

theorem poisson_limit_theorem:
  fixes p :: "nat \<Rightarrow> real"
    and r :: real
    and k :: nat
  assumes scaled_probability_limit:
    "(\<lambda>n. real n * p n) \<longlonglongrightarrow> r"
  shows
    "(\<lambda>n.
        real (n choose k) * (p n) ^ k * (1 - p n) ^ (n - k))
      \<longlonglongrightarrow> exp (-r) * (r ^ k) / fact k"
  sorry

end
