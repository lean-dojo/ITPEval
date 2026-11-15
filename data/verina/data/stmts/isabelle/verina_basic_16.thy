(*
  Statement-only formalization of VERINA corpus artifact verina_basic_16,
  catalog title "replaceChars": an executable Unicode-scalar string program
  replaces every occurrence of one character with another, together with its
  trivial precondition, pointwise postcondition, and correctness contract.
  This file contains no proof.
*)

theory verina_basic_16
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

definition replaceChars_precond ::
    "lean_string \<Rightarrow> lean_char \<Rightarrow> lean_char \<Rightarrow> bool" where
  "replaceChars_precond s oldChar newChar \<longleftrightarrow> True"

definition replaceChars_toList ::
    "lean_string \<Rightarrow> lean_char list" where
  "replaceChars_toList s = s"

definition replaceChars_mk ::
    "lean_char list \<Rightarrow> lean_string" where
  "replaceChars_mk chars = chars"

definition replaceChars ::
    "lean_string \<Rightarrow> lean_char \<Rightarrow> lean_char \<Rightarrow> lean_string" where
  "replaceChars s oldChar newChar =
    replaceChars_mk
      (map
        (\<lambda>c. if c = oldChar then newChar else c)
        (replaceChars_toList s))"

definition replaceChars_postcond ::
    "lean_string \<Rightarrow> lean_char \<Rightarrow> lean_char \<Rightarrow>
      lean_string \<Rightarrow> bool" where
  "replaceChars_postcond s oldChar newChar result \<longleftrightarrow>
    length result = length s \<and>
    (\<forall>i<length (replaceChars_toList s).
      ((replaceChars_toList s ! i = oldChar \<longrightarrow>
        replaceChars_toList result ! i = newChar) \<and>
       (replaceChars_toList s ! i \<noteq> oldChar \<longrightarrow>
        replaceChars_toList result ! i = replaceChars_toList s ! i)))"

theorem replaceChars_spec_satisfied:
  assumes "replaceChars_precond s oldChar newChar"
  shows
    "replaceChars_postcond s oldChar newChar
      (replaceChars s oldChar newChar)"
  sorry

end
