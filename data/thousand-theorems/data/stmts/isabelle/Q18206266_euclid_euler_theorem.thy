(*
  Statement-only formalization of thousand-theorems corpus artifact Q18206266
  (thousand-theorems__isabelle__Q18206266), "Euclid–Euler theorem": every even
  perfect natural number is a power of two times a prime Mersenne number.
  This file contains no proof.
*)

theory Q18206266_euclid_euler_theorem
  imports Main
begin

definition q18206266_perfect :: "nat \<Rightarrow> bool" where
  "q18206266_perfect n \<longleftrightarrow>
    (\<Sum>d\<in>{d. 1 \<le> d \<and> d < n \<and> d dvd n}. d) = n \<and> 0 < n"

theorem euclid_euler_theorem:
  fixes n :: nat
  assumes "even n"
    and "q18206266_perfect n"
  shows
    "\<exists>k::nat. prime ((2::nat) ^ (k + 1) - 1) \<and>
      n = 2 ^ k * (2 ^ (k + 1) - 1)"
  sorry

end
