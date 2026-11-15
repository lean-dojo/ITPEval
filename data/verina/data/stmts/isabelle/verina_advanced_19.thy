(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_19,
  catalog title "isCleanPalindrome": an executable Unicode-scalar string
  program keeps ASCII letters, lowercases ASCII capitals, and decides whether
  the resulting character list is a palindrome. This file contains no proof.
*)

theory verina_advanced_19
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

definition isUpperAlpha :: "lean_char \<Rightarrow> bool" where
  "isUpperAlpha c \<longleftrightarrow>
    65 \<le> lean_char_to_nat c \<and> lean_char_to_nat c \<le> 90"

definition isLowerAlpha :: "lean_char \<Rightarrow> bool" where
  "isLowerAlpha c \<longleftrightarrow>
    97 \<le> lean_char_to_nat c \<and> lean_char_to_nat c \<le> 122"

definition isAlpha :: "lean_char \<Rightarrow> bool" where
  "isAlpha c \<longleftrightarrow> isUpperAlpha c \<or> isLowerAlpha c"

definition toLower :: "lean_char \<Rightarrow> lean_char" where
  "toLower c =
    (if isUpperAlpha c
     then lean_low_char_of_nat (lean_char_to_nat c + 32)
     else c)"

definition normalizeChar :: "lean_char \<Rightarrow> lean_char option" where
  "normalizeChar c =
    (if isAlpha c then Some (toLower c) else None)"

fun normalizeString :: "lean_string \<Rightarrow> lean_char list" where
  "normalizeString [] = []"
| "normalizeString (c # cs) =
    (case normalizeChar c of
       Some c' \<Rightarrow> c' # normalizeString cs
     | None \<Rightarrow> normalizeString cs)"

definition isCleanPalindrome_precond :: "lean_string \<Rightarrow> bool" where
  "isCleanPalindrome_precond s \<longleftrightarrow> True"

definition reverseList :: "lean_char list \<Rightarrow> lean_char list" where
  "reverseList xs = rev xs"

definition isCleanPalindrome :: "lean_string \<Rightarrow> bool" where
  "isCleanPalindrome s =
    (let norm = normalizeString s
     in norm = reverseList norm)"

definition isCleanPalindrome_postcond ::
    "lean_string \<Rightarrow> bool \<Rightarrow> bool" where
  "isCleanPalindrome_postcond s result \<longleftrightarrow>
    (let norm = normalizeString s
     in (result = True \<longrightarrow> norm = rev norm) \<and>
        (result = False \<longrightarrow> norm \<noteq> rev norm))"

theorem isCleanPalindrome_spec_satisfied:
  assumes "isCleanPalindrome_precond s"
  shows "isCleanPalindrome_postcond s (isCleanPalindrome s)"
  sorry

end
