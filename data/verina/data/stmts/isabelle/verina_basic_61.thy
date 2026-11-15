(*
  Statement-only formalization of VERINA corpus artifact verina_basic_61
  (verina__isabelle__verina_basic_61), catalog title "allDigits": an
  executable Unicode-scalar string scan returns true exactly when every
  character is an ASCII decimal digit from zero through nine, together with
  its unconditional precondition, postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_61
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

definition isDigit :: "lean_char \<Rightarrow> bool" where
  "isDigit c \<longleftrightarrow>
    48 \<le> lean_char_to_nat c \<and> lean_char_to_nat c \<le> 57"

definition allDigits_precond :: "lean_string \<Rightarrow> bool" where
  "allDigits_precond s \<longleftrightarrow> True"

fun allDigits_loop :: "lean_string \<Rightarrow> bool" where
  "allDigits_loop [] = True"
| "allDigits_loop (c # cs) =
    (if \<not> isDigit c then False else allDigits_loop cs)"

definition allDigits :: "lean_string \<Rightarrow> bool" where
  "allDigits s = allDigits_loop s"

definition allDigits_postcond ::
    "lean_string \<Rightarrow> bool \<Rightarrow> bool" where
  "allDigits_postcond s result \<longleftrightarrow>
    (result = True \<longleftrightarrow> list_all isDigit s)"

theorem allDigits_spec_satisfied:
  assumes "allDigits_precond s"
  shows "allDigits_postcond s (allDigits s)"
  sorry

end
