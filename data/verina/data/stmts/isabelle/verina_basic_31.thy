(*
  Statement-only formalization of VERINA corpus artifact verina_basic_31
  (verina__isabelle__verina_basic_31), catalog title "toUppercase": an
  executable Unicode-scalar string program maps each ASCII lowercase
  character through truncated subtraction by 32 and reduction modulo 128,
  leaving every other character unchanged, together with its unconditional
  precondition, pointwise postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_31
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

definition lean_bits4_of_nat :: "nat \<Rightarrow> lean_bits4" where
  "lean_bits4_of_nat n =
    LeanBits4
      ((n div 8) mod 2 = 1)
      ((n div 4) mod 2 = 1)
      ((n div 2) mod 2 = 1)
      (n mod 2 = 1)"

definition lean_bits5_of_nat :: "nat \<Rightarrow> lean_bits5" where
  "lean_bits5_of_nat n =
    LeanBits5
      ((n div 16) mod 2 = 1)
      ((n div 8) mod 2 = 1)
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

definition lean_char_of_nat :: "nat \<Rightarrow> lean_char" where
  "lean_char_of_nat n =
    (if n < 55296 then lean_low_char_of_nat n
     else if n < 57344 then lean_low_char_of_nat 0
     else if n < 65536 then
       (let m = n - 57344
        in BMP_High
             (lean_bits5_of_nat (m div 256))
             (lean_byte_of_nat (m mod 256)))
     else if n < 1114112 then
       (let m = n - 65536
        in Supplementary
             (lean_bits4_of_nat (m div 65536))
             (lean_byte_of_nat ((m div 256) mod 256))
             (lean_byte_of_nat (m mod 256)))
     else lean_low_char_of_nat 0)"

definition isLowerCase :: "lean_char \<Rightarrow> bool" where
  "isLowerCase c \<longleftrightarrow>
    97 \<le> lean_char_to_nat c \<and> lean_char_to_nat c \<le> 122"

definition shiftMinus32 :: "lean_char \<Rightarrow> lean_char" where
  "shiftMinus32 c =
    lean_char_of_nat ((lean_char_to_nat c - 32) mod 128)"

definition toUppercase_precond :: "lean_string \<Rightarrow> bool" where
  "toUppercase_precond s \<longleftrightarrow> True"

definition toUppercase_toList :: "lean_string \<Rightarrow> lean_char list" where
  "toUppercase_toList s = s"

definition toUppercase_mk :: "lean_char list \<Rightarrow> lean_string" where
  "toUppercase_mk chars = chars"

definition toUppercase :: "lean_string \<Rightarrow> lean_string" where
  "toUppercase s =
    (let cs = toUppercase_toList s;
         cs' = map (\<lambda>c. if isLowerCase c then shiftMinus32 c else c) cs
     in toUppercase_mk cs')"

definition toUppercase_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "toUppercase_postcond s result \<longleftrightarrow>
    (let cs = toUppercase_toList s;
         cs' = toUppercase_toList result
     in length result = length s \<and>
        (\<forall>i. i < length s \<longrightarrow>
          ((isLowerCase (cs ! i) \<longrightarrow>
            cs' ! i = shiftMinus32 (cs ! i)) \<and>
           (\<not> isLowerCase (cs ! i) \<longrightarrow>
            cs' ! i = cs ! i))))"

theorem toUppercase_spec_satisfied:
  assumes "toUppercase_precond s"
  shows "toUppercase_postcond s (toUppercase s)"
  sorry

end
