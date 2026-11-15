(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_72,
  catalog title "singleDigitPrimeFactor": an executable natural-number program
  returns the first divisor among 2, 3, 5, and 7, or zero when none applies,
  together with its precondition and correctness contract. This file contains
  no proof.
*)

theory verina_advanced_72
  imports Main
begin

definition singleDigitPrimeFactor_precond :: "nat \<Rightarrow> bool" where
  "singleDigitPrimeFactor_precond n \<longleftrightarrow> True"

definition singleDigitPrimeFactor :: "nat \<Rightarrow> nat" where
  "singleDigitPrimeFactor n =
    (if n = 0 then 0
     else if n mod 2 = 0 then 2
     else if n mod 3 = 0 then 3
     else if n mod 5 = 0 then 5
     else if n mod 7 = 0 then 7
     else 0)"

definition singleDigitPrimeFactor_postcond ::
    "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "singleDigitPrimeFactor_postcond n result \<longleftrightarrow>
    result \<in> set [0, 2, 3, 5, 7] \<and>
    (result = 0 \<longrightarrow>
      (n = 0 \<or> (\<forall>d\<in>set [2, 3, 5, 7]. n mod d \<noteq> 0))) \<and>
    (result \<noteq> 0 \<longrightarrow>
      n \<noteq> 0 \<and>
      n mod result = 0 \<and>
      (\<forall>x<result.
        x \<in> set [2, 3, 5, 7] \<longrightarrow> n mod x \<noteq> 0))"

theorem singleDigitPrimeFactor_spec_satisfied:
  assumes "singleDigitPrimeFactor_precond n"
  shows "singleDigitPrimeFactor_postcond n (singleDigitPrimeFactor n)"
  sorry

end
