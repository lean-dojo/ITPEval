(*
  Statement-only formalization of the thousand-theorems corpus artifact Q914517
  (thousand-theorems__isabelle__Q914517), "Fermat's theorem on sums of two
  squares": every prime natural number not congruent to 3 modulo 4 is a sum of
  two squares of natural numbers. This file contains no proof.
*)

theory Q914517_fermat_s_theorem_on_sums_of_two_squares
  imports Main
begin

definition q914517_prime :: "nat \<Rightarrow> bool" where
  "q914517_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d::nat. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

theorem fermat_sum_of_two_squares:
  fixes p :: nat
  assumes "q914517_prime p"
    and "p mod 4 \<noteq> 3"
  shows "\<exists>a b :: nat. a ^ 2 + b ^ 2 = p"
  sorry

end
