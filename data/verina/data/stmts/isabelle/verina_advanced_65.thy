(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_65,
  catalog title "reverseString": an executable Unicode-scalar string program
  reverses its input with a tail-recursive character-list accumulator, together
  with its precondition, exact reversal postcondition, and correctness contract.
  This file contains no proof.
*)

theory verina_advanced_65
  imports Main
begin

datatype lean_trit = Trit0 | Trit1 | Trit2

datatype lean_bits3 = LeanBits3 bool bool bool

datatype lean_bits4 = LeanBits4 bool bool bool bool

datatype lean_bits5 = LeanBits5 bool bool bool bool bool

datatype lean_byte = LeanByte bool bool bool bool bool bool bool bool

datatype lean_char =
    BMP_Low lean_trit lean_trit lean_trit lean_bits3 lean_byte
  | BMP_High lean_bits5 lean_byte
  | Supplementary lean_bits4 lean_byte lean_byte

type_synonym lean_string = "lean_char list"

definition reverseString_precond :: "lean_string \<Rightarrow> bool" where
  "reverseString_precond s \<longleftrightarrow> True"

definition reverseString_toList ::
    "lean_string \<Rightarrow> lean_char list" where
  "reverseString_toList s = s"

definition reverseString_mk ::
    "lean_char list \<Rightarrow> lean_string" where
  "reverseString_mk chars = chars"

fun reverseString_reverseAux ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> lean_char list" where
  "reverseString_reverseAux [] acc = acc"
| "reverseString_reverseAux (h # t) acc =
    reverseString_reverseAux t (h # acc)"

definition reverseString :: "lean_string \<Rightarrow> lean_string" where
  "reverseString s =
    reverseString_mk
      (reverseString_reverseAux (reverseString_toList s) [])"

definition reverseString_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "reverseString_postcond s result \<longleftrightarrow>
    length result = length s \<and>
    reverseString_toList result = rev (reverseString_toList s)"

theorem reverseString_spec_satisfied:
  assumes "reverseString_precond s"
  shows "reverseString_postcond s (reverseString s)"
  sorry

end
