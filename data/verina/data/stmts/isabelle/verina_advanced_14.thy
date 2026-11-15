(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_14,
  catalog title "ifPowerOfFour": an executable natural-number program decides
  whether its input is a power of four, together with its precondition and
  Boolean correctness contract. This file contains no proof.
*)

theory verina_advanced_14
  imports Main
begin

definition ifPowerOfFour_precond :: "nat \<Rightarrow> bool" where
  "ifPowerOfFour_precond n \<longleftrightarrow> True"

fun ifPowerOfFour_helper :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "ifPowerOfFour_helper 0 n = False"
| "ifPowerOfFour_helper (Suc fuel) 0 = False"
| "ifPowerOfFour_helper (Suc fuel) (Suc 0) = True"
| "ifPowerOfFour_helper (Suc fuel) (Suc (Suc l)) =
    (if (l + 2) mod 4 = 0
     then ifPowerOfFour_helper fuel ((l + 2) div 4)
     else False)"

definition ifPowerOfFour :: "nat \<Rightarrow> bool" where
  "ifPowerOfFour n = ifPowerOfFour_helper (Suc n) n"

definition ifPowerOfFour_postcond :: "nat \<Rightarrow> bool \<Rightarrow> bool" where
  "ifPowerOfFour_postcond n result \<longleftrightarrow>
    (result \<longleftrightarrow> (\<exists>m. n = 4 ^ m))"

theorem ifPowerOfFour_spec_satisfied:
  assumes "ifPowerOfFour_precond n"
  shows "ifPowerOfFour_postcond n (ifPowerOfFour n)"
  sorry

end
