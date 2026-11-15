(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_7,
  catalog title "binaryToDecimal": an executable recursive program converts a
  big-endian list of binary natural-number digits to its decimal value, with
  its binary-digit precondition and fold-based equality postcondition. This
  file contains no proof.
*)

theory verina_advanced_7
  imports Main
begin

definition binaryToDecimal_precond :: "nat list \<Rightarrow> bool" where
  "binaryToDecimal_precond digits \<longleftrightarrow>
    list_all (\<lambda>d. d = 0 \<or> d = 1) digits"

fun binaryToDecimal_helper :: "nat list \<Rightarrow> nat" where
  "binaryToDecimal_helper [] = 0"
| "binaryToDecimal_helper (first # rest) =
    first * 2 ^ length rest + binaryToDecimal_helper rest"

definition binaryToDecimal :: "nat list \<Rightarrow> nat" where
  "binaryToDecimal digits = binaryToDecimal_helper digits"

definition binaryToDecimal_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "binaryToDecimal_postcond digits result \<longleftrightarrow>
    result - foldl (\<lambda>acc bit. acc * 2 + bit) 0 digits = 0 \<and>
    foldl (\<lambda>acc bit. acc * 2 + bit) 0 digits - result = 0"

theorem binaryToDecimal_spec_satisfied:
  assumes "binaryToDecimal_precond digits"
  shows "binaryToDecimal_postcond digits (binaryToDecimal digits)"
  sorry

end
