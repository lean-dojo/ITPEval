(*
  Statement-only formalization of thousand-theorems corpus artifact Q1506253
  (thousand-theorems__isabelle__Q1506253), "Euclid's theorem": for every
  natural number, there is a prime natural number at least as large. This file
  contains no proof.
*)

theory Q1506253_euclid_s_theorem
  imports Main
begin

definition q1506253_prime :: "nat \<Rightarrow> bool" where
  "q1506253_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d::nat. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

theorem euclid_s_theorem:
  "\<forall>n::nat. \<exists>p::nat. n \<le> p \<and> q1506253_prime p"
  sorry

end
