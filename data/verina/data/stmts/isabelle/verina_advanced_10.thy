(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_10,
  catalog title "findExponents": exact operational graph relations model the
  program that removes listed prime factors and returns each listed prime with
  its exponent, under the prime-factorization precondition and postcondition.
  This file contains no proof.
*)

theory verina_advanced_10
  imports Main
begin

definition nat_prime :: "nat \<Rightarrow> bool" where
  "nat_prime p \<longleftrightarrow>
    p > 1 \<and> (\<forall>d. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

inductive removePrimeFactor :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  remove_invalid:
    "p \<le> 1 \<or> n = 0 \<Longrightarrow> removePrimeFactor n p n"
| remove_indivisible:
    "p > 1 \<Longrightarrow>
     n > 0 \<Longrightarrow>
     n mod p \<noteq> 0 \<Longrightarrow>
     removePrimeFactor n p n"
| remove_divisible:
    "p > 1 \<Longrightarrow>
     n > 0 \<Longrightarrow>
     n mod p = 0 \<Longrightarrow>
     removePrimeFactor (n div p) p result \<Longrightarrow>
     removePrimeFactor n p result"

inductive removeAllPrimeFactors ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool" where
  remove_all_Nil:
    "removeAllPrimeFactors n [] n"
| remove_all_Cons:
    "removePrimeFactor n p n' \<Longrightarrow>
     removeAllPrimeFactors n' ps result \<Longrightarrow>
     removeAllPrimeFactors n (p # ps) result"

definition findExponents_precond :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "findExponents_precond n primes \<longleftrightarrow>
    n > 0 \<and>
    length primes > 0 \<and>
    list_all nat_prime primes \<and>
    distinct primes \<and>
    removeAllPrimeFactors n primes 1"

inductive countFactor ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  count_zero:
    "countFactor 0 p count (count, 0)"
| count_invalid:
    "n > 0 \<Longrightarrow>
     p \<le> 1 \<Longrightarrow>
     countFactor n p count (count, n)"
| count_indivisible:
    "n > 0 \<Longrightarrow>
     p > 1 \<Longrightarrow>
     n mod p \<noteq> 0 \<Longrightarrow>
     countFactor n p count (count, n)"
| count_divisible:
    "n > 0 \<Longrightarrow>
     p > 1 \<Longrightarrow>
     n mod p = 0 \<Longrightarrow>
     countFactor (n div p) p (count + 1) result \<Longrightarrow>
     countFactor n p count result"

inductive countFactors ::
    "nat \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
  count_factors_Nil:
    "countFactors n [] []"
| count_factors_Cons:
    "countFactor n p 0 (count, n') \<Longrightarrow>
     countFactors n' ps result \<Longrightarrow>
     countFactors n (p # ps) ((p, count) # result)"

definition findExponents ::
    "nat \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
  "findExponents n primes result \<longleftrightarrow>
    countFactors n primes result"

definition findExponents_postcond ::
    "nat \<Rightarrow> nat list \<Rightarrow> (nat \<times> nat) list \<Rightarrow> bool" where
  "findExponents_postcond n primes result \<longleftrightarrow>
    n = foldl (\<lambda>acc pe. acc * fst pe ^ snd pe) 1 result \<and>
    list_all (\<lambda>pe. fst pe \<in> set primes) result \<and>
    list_all (\<lambda>p. \<exists>pe \<in> set result. fst pe = p) primes"

theorem findExponents_spec_satisfied:
  assumes "findExponents_precond n primes"
  shows "\<forall>result.
    findExponents n primes result \<longrightarrow>
    findExponents_postcond n primes result"
  sorry

end
