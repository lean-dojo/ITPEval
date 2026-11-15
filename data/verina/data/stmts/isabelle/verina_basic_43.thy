(*
  Statement-only formalization of VERINA corpus artifact verina_basic_43
  (verina__isabelle__verina_basic_43), catalog title
  "sumOfFourthPowerOfOddNumbers": an executable natural-number recursion sums
  the fourth powers of the first n odd numbers, together with its
  unconditional precondition, closed-form postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_43
  imports Main
begin

definition sumOfFourthPowerOfOddNumbers_precond :: "nat \<Rightarrow> bool" where
  "sumOfFourthPowerOfOddNumbers_precond n \<longleftrightarrow> True"

fun sumOfFourthPowerOfOddNumbers :: "nat \<Rightarrow> nat" where
  "sumOfFourthPowerOfOddNumbers 0 = 0"
| "sumOfFourthPowerOfOddNumbers (Suc n) =
    sumOfFourthPowerOfOddNumbers n + (2 * n + 1) ^ 4"

definition sumOfFourthPowerOfOddNumbers_postcond ::
    "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "sumOfFourthPowerOfOddNumbers_postcond n result \<longleftrightarrow>
    15 * result =
      n * (2 * n + 1) * (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n)"

theorem sumOfFourthPowerOfOddNumbers_spec_satisfied:
  assumes "sumOfFourthPowerOfOddNumbers_precond n"
  shows
    "sumOfFourthPowerOfOddNumbers_postcond
      n (sumOfFourthPowerOfOddNumbers n)"
  sorry

end
