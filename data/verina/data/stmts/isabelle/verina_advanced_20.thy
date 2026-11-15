(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_20,
  catalog title "isItEight": an executable integer program returns true
  exactly when the input is divisible by 8 or its absolute value has decimal
  digit 8, together with its precondition and correctness contract. This file
  contains no proof.
*)

theory verina_advanced_20
  imports Main
begin

definition isItEight_precond :: "int \<Rightarrow> bool" where
  "isItEight_precond n \<longleftrightarrow> True"

fun hasDigitEight_go :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "hasDigitEight_go 0 m = False"
| "hasDigitEight_go (Suc fuel) m =
    (if m = 0
     then False
     else if m mod 10 = 8
     then True
     else hasDigitEight_go fuel (m div 10))"

definition hasDigitEight :: "nat \<Rightarrow> bool" where
  "hasDigitEight m = hasDigitEight_go (Suc m) m"

definition isItEight :: "int \<Rightarrow> bool" where
  "isItEight n =
    (n mod 8 = 0 \<or> hasDigitEight (nat (abs n)))"

definition isItEight_postcond :: "int \<Rightarrow> bool \<Rightarrow> bool" where
  "isItEight_postcond n result \<longleftrightarrow>
    ((n mod 8 = 0 \<or>
      (\<exists>i::nat. nat (abs n) div (10 ^ i) mod 10 = 8))
     \<longleftrightarrow> result)"

theorem isItEight_spec_satisfied:
  assumes "isItEight_precond n"
  shows "isItEight_postcond n (isItEight n)"
  sorry

end
