(*
  Statement-only formalization of VERINA corpus artifact verina_basic_18,
  catalog title "sumOfDigits": an executable natural-number program repeatedly
  extracts base-10 digits and returns their sum, together with its trivial
  precondition, decimal-representation postcondition, and correctness
  contract. This file contains no proof.
*)

theory verina_basic_18
  imports Main
begin

definition sumOfDigits_precond :: "nat \<Rightarrow> bool" where
  "sumOfDigits_precond n \<longleftrightarrow> True"

fun sumOfDigits_loop ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sumOfDigits_loop 0 n acc = acc"
| "sumOfDigits_loop (Suc fuel) n acc =
    (if n = 0
     then acc
     else sumOfDigits_loop fuel (n div 10) (acc + n mod 10))"

definition sumOfDigits :: "nat \<Rightarrow> nat" where
  "sumOfDigits n = sumOfDigits_loop (Suc n) n 0"

fun decimalDigitsRev_go :: "nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "decimalDigitsRev_go 0 n = []"
| "decimalDigitsRev_go (Suc fuel) n =
    (if n = 0
     then []
     else (n mod 10) # decimalDigitsRev_go fuel (n div 10))"

definition decimalDigitValues :: "nat \<Rightarrow> nat list" where
  "decimalDigitValues n =
    (if n = 0
     then [0]
     else rev (decimalDigitsRev_go (Suc n) n))"

definition decimalRepresentationDigitSum :: "nat \<Rightarrow> nat" where
  "decimalRepresentationDigitSum n = sum_list (decimalDigitValues n)"

definition sumOfDigits_postcond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "sumOfDigits_postcond n result \<longleftrightarrow>
    result - decimalRepresentationDigitSum n = 0 \<and>
    decimalRepresentationDigitSum n - result = 0"

theorem sumOfDigits_spec_satisfied:
  assumes "sumOfDigits_precond n"
  shows "sumOfDigits_postcond n (sumOfDigits n)"
  sorry

end
