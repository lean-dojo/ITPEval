(*
  Statement-only formalization of VERINA corpus artifact verina_basic_28
  (verina__isabelle__verina_basic_28), catalog title "isPrime": an executable
  fuel-bounded divisor search returns whether a natural number at least two
  has no divisor from two to below the input, together with its precondition,
  Boolean postcondition, and final correctness proposition. This file contains
  no proof.
*)

theory verina_basic_28
  imports Main
begin

definition isPrime_precond :: "nat \<Rightarrow> bool" where
  "isPrime_precond n \<longleftrightarrow> n \<ge> 2"

fun isPrime_check :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isPrime_check n i 0 = True"
| "isPrime_check n i (Suc fuel) =
    (if i * i > n
     then True
     else if n mod i = 0
          then False
          else isPrime_check n (i + 1) fuel)"

definition isPrime :: "nat \<Rightarrow> bool" where
  "isPrime n = isPrime_check n 2 n"

definition isPrime_postcond :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "isPrime_postcond n result \<longleftrightarrow>
    ((result \<longrightarrow>
        list_all (\<lambda>k. n mod k \<noteq> 0) [2..<2 + (n - 2)]) \<and>
     (\<not> result \<longrightarrow>
        list_ex (\<lambda>k. n mod k = 0) [2..<2 + (n - 2)]))"

theorem isPrime_spec_satisfied:
  fixes n :: nat
  assumes "isPrime_precond n"
  shows "isPrime_postcond n (isPrime n)"
  sorry

end
