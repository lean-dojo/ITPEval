(*
  Statement-only formalization of thousand-theorems corpus artifact Q670235
  (thousand-theorems__isabelle__Q670235), "Fundamental theorem of arithmetic":
  every list of prime natural numbers with product n has the canonical prime
  factorization multiset of n. This file contains no proof.
*)

theory Q670235_fundamental_theorem_of_arithmetic
  imports Main
begin

theorem primeFactorsList_unique:
  fixes n :: nat
    and l :: "nat list"
  assumes product: "prod_list l = n"
    and primes: "\<And>p. p \<in> set l \<Longrightarrow> prime p"
  shows "mset l = prime_factorization n"
  sorry

end
