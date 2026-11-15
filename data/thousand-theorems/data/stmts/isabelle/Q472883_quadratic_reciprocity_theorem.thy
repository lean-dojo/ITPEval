(*
  Statement-only formalization of thousand-theorems corpus artifact Q472883
  (thousand-theorems__isabelle__Q472883), "Quadratic reciprocity theorem":
  the Legendre symbols of two distinct odd primes, and more generally the
  Jacobi symbols of two odd natural numbers, differ by the standard
  quadratic-reciprocity sign. This file contains no proof.
*)

theory Q472883_quadratic_reciprocity_theorem
  imports Main
begin

definition q472883_prime :: "nat \<Rightarrow> bool" where
  "q472883_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

definition q472883_legendre_symbol :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "q472883_legendre_symbol a p =
    (if a mod int p = 0 then 0
     else if (\<exists>y::int. y ^ 2 mod int p = a mod int p) then 1
     else -1)"

definition q472883_prime_multiplicity :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q472883_prime_multiplicity p n =
    (if n = 0 then 0 else Max {k::nat. p ^ k dvd n})"

definition q472883_jacobi_symbol :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "q472883_jacobi_symbol a b =
    (\<Prod>p\<in>{p. p \<le> b \<and> q472883_prime p}.
      q472883_legendre_symbol a p ^ q472883_prime_multiplicity p b)"

theorem legendre_quadratic_reciprocity:
  fixes p q :: nat
  assumes "q472883_prime p"
    and "q472883_prime q"
    and "p \<noteq> 2"
    and "q \<noteq> 2"
    and "p \<noteq> q"
  shows
    "q472883_legendre_symbol (int p) q *
        q472883_legendre_symbol (int q) p =
      (-1 :: int) ^ (p div 2 * (q div 2))"
  sorry

theorem jacobi_quadratic_reciprocity:
  fixes a b :: nat
  assumes "odd a"
    and "odd b"
  shows
    "q472883_jacobi_symbol (int a) b =
      (-1 :: int) ^ (a div 2 * (b div 2)) *
        q472883_jacobi_symbol (int b) a"
  sorry

end
