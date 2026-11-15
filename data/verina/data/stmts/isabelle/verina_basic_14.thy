(*
  Statement-only formalization of VERINA corpus artifact verina_basic_14,
  catalog title "containsZ": an executable Unicode-scalar string program
  returns true exactly when the input contains lowercase or uppercase Z,
  together with its trivial precondition and Boolean correctness contract.
  This file contains no proof.
*)

theory verina_basic_14
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

definition lean_trit_of_nat :: "nat \<Rightarrow> lean_trit" where
  "lean_trit_of_nat n =
    (if n mod 3 = 0 then Trit0
     else if n mod 3 = 1 then Trit1
     else Trit2)"

definition lean_bits3_of_nat :: "nat \<Rightarrow> lean_bits3" where
  "lean_bits3_of_nat n =
    LeanBits3
      ((n div 4) mod 2 = 1)
      ((n div 2) mod 2 = 1)
      (n mod 2 = 1)"

definition lean_byte_of_nat :: "nat \<Rightarrow> lean_byte" where
  "lean_byte_of_nat n =
    LeanByte
      ((n div 128) mod 2 = 1)
      ((n div 64) mod 2 = 1)
      ((n div 32) mod 2 = 1)
      ((n div 16) mod 2 = 1)
      ((n div 8) mod 2 = 1)
      ((n div 4) mod 2 = 1)
      ((n div 2) mod 2 = 1)
      (n mod 2 = 1)"

definition lean_low_char_of_nat :: "nat \<Rightarrow> lean_char" where
  "lean_low_char_of_nat n =
    (let q = n div 2048
     in BMP_Low
          (lean_trit_of_nat (q div 9))
          (lean_trit_of_nat ((q div 3) mod 3))
          (lean_trit_of_nat (q mod 3))
          (lean_bits3_of_nat ((n div 256) mod 8))
          (lean_byte_of_nat (n mod 256)))"

abbreviation ascii :: "nat \<Rightarrow> lean_char" where
  "ascii n \<equiv> lean_low_char_of_nat n"

definition containsZ_precond :: "lean_string \<Rightarrow> bool" where
  "containsZ_precond s \<longleftrightarrow> True"

definition containsZ :: "lean_string \<Rightarrow> bool" where
  "containsZ s =
    list_ex (\<lambda>c. c = ascii 122 \<or> c = ascii 90) s"

definition containsZ_postcond ::
    "lean_string \<Rightarrow> bool \<Rightarrow> bool" where
  "containsZ_postcond s result \<longleftrightarrow>
    ((\<exists>x\<in>set s. x = ascii 122 \<or> x = ascii 90)
      \<longleftrightarrow> result)"

theorem containsZ_spec_satisfied:
  assumes "containsZ_precond s"
  shows "containsZ_postcond s (containsZ s)"
  sorry

end
