(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3527230 (thousand-theorems__isabelle__Q3527230), "Von Staudt–Clausen
  theorem": for every natural number k, the Bernoulli number indexed by 2k,
  after adding the reciprocals of the relevant primes, is an integer. This file
  contains no proof.
*)

theory Q3527230_von_staudt_clausen_theorem
  imports Main HOL.Rat
begin

definition q3527230_prime :: "nat \<Rightarrow> bool" where
  "q3527230_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d::nat. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

fun q3527230_bernoulli_values :: "nat \<Rightarrow> rat list" where
  "q3527230_bernoulli_values 0 = []"
| "q3527230_bernoulli_values (Suc n) =
    q3527230_bernoulli_values n @
      [1 - (\<Sum>j<n.
        of_nat (n choose j) / of_nat (n - j + 1) *
          q3527230_bernoulli_values n ! j)]"

definition q3527230_bernoulli_positive :: "nat \<Rightarrow> rat" where
  "q3527230_bernoulli_positive n =
    q3527230_bernoulli_values (Suc n) ! n"

definition q3527230_bernoulli :: "nat \<Rightarrow> rat" where
  "q3527230_bernoulli n =
    (-1) ^ n * q3527230_bernoulli_positive n"

theorem q3527230_von_staudt_clausen:
  fixes k :: nat
  shows
    "\<exists>z::int.
      q3527230_bernoulli (2 * k) +
        (\<Sum>p<2 * k + 2.
          if q3527230_prime p \<and> p - 1 dvd 2 * k then
            (1::rat) / of_nat p
          else 0)
        = of_int z"
  sorry

end
