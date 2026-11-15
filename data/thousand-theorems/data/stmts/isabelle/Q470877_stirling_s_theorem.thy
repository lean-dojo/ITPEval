(*
  Statement-only formalization of thousand-theorems corpus artifact Q470877,
  "Stirling's theorem": the factorial-normalized Stirling sequence converges
  to the square root of pi. This file contains no proof.
*)

theory Q470877_stirling_s_theorem
  imports Complex_Main
begin

definition stirling_seq :: "nat \<Rightarrow> real" where
  "stirling_seq n =
    real (fact n) / (sqrt (2 * real n) * (real n / exp 1) ^ n)"

theorem tendsto_stirling_seq_sqrt_pi:
  "stirling_seq \<longlonglongrightarrow> sqrt pi"
  sorry

end
