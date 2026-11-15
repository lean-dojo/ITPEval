(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_6,
  catalog title "allVowels": an executable Unicode-scalar string program
  lowercases ASCII capitals and checks whether all five lowercase English
  vowels occur in the normalized string. This file contains no proof.
*)

theory verina_advanced_6
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

definition lean_bit_value :: "bool \<Rightarrow> nat" where
  "lean_bit_value b = (if b then 1 else 0)"

fun lean_trit_value :: "lean_trit \<Rightarrow> nat" where
  "lean_trit_value Trit0 = 0"
| "lean_trit_value Trit1 = 1"
| "lean_trit_value Trit2 = 2"

fun lean_bits3_value :: "lean_bits3 \<Rightarrow> nat" where
  "lean_bits3_value (LeanBits3 b2 b1 b0) =
    (lean_bit_value b2 * 2 + lean_bit_value b1) * 2 +
    lean_bit_value b0"

fun lean_bits4_value :: "lean_bits4 \<Rightarrow> nat" where
  "lean_bits4_value (LeanBits4 b3 b2 b1 b0) =
    ((lean_bit_value b3 * 2 + lean_bit_value b2) * 2 +
      lean_bit_value b1) * 2 + lean_bit_value b0"

fun lean_bits5_value :: "lean_bits5 \<Rightarrow> nat" where
  "lean_bits5_value (LeanBits5 b4 b3 b2 b1 b0) =
    (((lean_bit_value b4 * 2 + lean_bit_value b3) * 2 +
       lean_bit_value b2) * 2 + lean_bit_value b1) * 2 +
    lean_bit_value b0"

fun lean_byte_value :: "lean_byte \<Rightarrow> nat" where
  "lean_byte_value (LeanByte b7 b6 b5 b4 b3 b2 b1 b0) =
    (((((((lean_bit_value b7 * 2 + lean_bit_value b6) * 2 +
          lean_bit_value b5) * 2 + lean_bit_value b4) * 2 +
        lean_bit_value b3) * 2 + lean_bit_value b2) * 2 +
      lean_bit_value b1) * 2 + lean_bit_value b0)"

fun lean_char_to_nat :: "lean_char \<Rightarrow> nat" where
  "lean_char_to_nat (BMP_Low t2 t1 t0 bits byte) =
    ((((lean_trit_value t2 * 3 + lean_trit_value t1) * 3 +
        lean_trit_value t0) * 8 + lean_bits3_value bits) * 256 +
      lean_byte_value byte)"
| "lean_char_to_nat (BMP_High bits byte) =
    57344 + lean_bits5_value bits * 256 + lean_byte_value byte"
| "lean_char_to_nat (Supplementary bits high low) =
    65536 + lean_bits4_value bits * 65536 +
    lean_byte_value high * 256 + lean_byte_value low"

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

definition toLower :: "lean_char \<Rightarrow> lean_char" where
  "toLower c =
    (if 65 \<le> lean_char_to_nat c \<and> lean_char_to_nat c \<le> 90
     then lean_low_char_of_nat (lean_char_to_nat c + 32)
     else c)"

definition normalize_str :: "lean_string \<Rightarrow> lean_char list" where
  "normalize_str s = map toLower s"

definition allVowels_precond :: "lean_string \<Rightarrow> bool" where
  "allVowels_precond s \<longleftrightarrow> True"

definition allVowels :: "lean_string \<Rightarrow> bool" where
  "allVowels s =
    (let chars = normalize_str s;
         vowelSet = [ascii 97, ascii 101, ascii 105, ascii 111, ascii 117]
     in list_all (\<lambda>v. v \<in> set chars) vowelSet)"

definition allVowels_postcond ::
    "lean_string \<Rightarrow> bool \<Rightarrow> bool" where
  "allVowels_postcond s result \<longleftrightarrow>
    (let chars = normalize_str s
     in result \<longleftrightarrow>
       list_all
         (\<lambda>v. v \<in> set chars)
         [ascii 97, ascii 101, ascii 105, ascii 111, ascii 117])"

theorem allVowels_spec_satisfied:
  assumes "allVowels_precond s"
  shows "allVowels_postcond s (allVowels s)"
  sorry

end
