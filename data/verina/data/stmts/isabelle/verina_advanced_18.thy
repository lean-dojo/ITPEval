(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_18,
  catalog title "isArmstrong": an executable natural-number program counts
  decimal digits, sums each digit raised to that count, and decides the
  Armstrong-number property together with its correctness contract. This file
  contains no proof.
*)

theory verina_advanced_18
  imports Main
begin

fun countDigits_go :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "countDigits_go 0 n acc = acc"
| "countDigits_go (Suc fuel) n acc =
    (if n = 0
     then acc
     else countDigits_go fuel (n div 10) (acc + 1))"

definition countDigits :: "nat \<Rightarrow> nat" where
  "countDigits n =
    countDigits_go (Suc n) n (if n = 0 then 1 else 0)"

definition isArmstrong_precond :: "nat \<Rightarrow> bool" where
  "isArmstrong_precond n \<longleftrightarrow> True"

fun sumPowers_go ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sumPowers_go 0 n k acc = acc"
| "sumPowers_go (Suc fuel) n k acc =
    (if n = 0
     then acc
     else
       (let digit = n mod 10
        in sumPowers_go fuel (n div 10) k (acc + digit ^ k)))"

definition sumPowers :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sumPowers n k = sumPowers_go (Suc n) n k 0"

definition isArmstrong :: "nat \<Rightarrow> bool" where
  "isArmstrong n = (let k = countDigits n in sumPowers n k = n)"

fun decimalDigitsRev_go :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "decimalDigitsRev_go 0 n = []"
| "decimalDigitsRev_go (Suc fuel) n =
    (if n = 0
     then []
     else (n mod 10) # decimalDigitsRev_go fuel (n div 10))"

definition decimalDigits :: "nat \<Rightarrow> nat list" where
  "decimalDigits n =
    (if n = 0
     then [0]
     else rev (decimalDigitsRev_go (Suc n) n))"

definition isArmstrong_postcond :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "isArmstrong_postcond n result \<longleftrightarrow>
    (let n' =
       foldl
         (\<lambda>acc d. acc + d ^ countDigits n)
         0
         (decimalDigits n)
     in (result \<longrightarrow> n = n') \<and>
        (\<not> result \<longrightarrow> n \<noteq> n'))"

theorem isArmstrong_spec_satisfied:
  assumes "isArmstrong_precond n"
  shows "isArmstrong_postcond n (isArmstrong n)"
  sorry

end
