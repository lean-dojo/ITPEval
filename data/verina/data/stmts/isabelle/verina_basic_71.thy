(*
  Statement-only formalization of VERINA corpus artifact verina_basic_71
  (verina__isabelle__verina_basic_71), catalog title
  "LongestCommonPrefix": an executable Unicode-scalar list program computes
  the longest shared initial segment of two character lists, together with
  its unconditional precondition, maximal-prefix postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_71
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

definition LongestCommonPrefix_precond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "LongestCommonPrefix_precond str1 str2 \<longleftrightarrow> True"

fun lean_list_get ::
    "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "lean_list_get [] n = None"
| "lean_list_get (x # xs) 0 = Some x"
| "lean_list_get (x # xs) (Suc n) = lean_list_get xs n"

fun LongestCommonPrefix_aux ::
    "nat \<Rightarrow> lean_string \<Rightarrow> lean_string \<Rightarrow>
      nat \<Rightarrow> lean_string \<Rightarrow> lean_string" where
  "LongestCommonPrefix_aux 0 str1 str2 idx acc = acc"
| "LongestCommonPrefix_aux (Suc fuel) str1 str2 idx acc =
    (case lean_list_get str1 idx of
       None \<Rightarrow> acc
     | Some c1 \<Rightarrow>
         (case lean_list_get str2 idx of
            None \<Rightarrow> acc
          | Some c2 \<Rightarrow>
              (if c1 \<noteq> c2
               then acc
               else LongestCommonPrefix_aux
                 fuel str1 str2 (Suc idx) (acc @ [c1]))))"

definition LongestCommonPrefix ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> lean_string" where
  "LongestCommonPrefix str1 str2 =
    LongestCommonPrefix_aux
      (min (length str1) (length str2)) str1 str2 0 []"

definition LongestCommonPrefix_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> lean_string \<Rightarrow> bool"
    where
  "LongestCommonPrefix_postcond str1 str2 result \<longleftrightarrow>
    length result \<le> length str1 \<and>
    result = take (length result) str1 \<and>
    length result \<le> length str2 \<and>
    result = take (length result) str2 \<and>
    (length result = length str1 \<or>
     length result = length str2 \<or>
     lean_list_get str1 (length result) \<noteq>
       lean_list_get str2 (length result))"

theorem LongestCommonPrefix_spec_satisfied:
  fixes str1 str2 :: lean_string
  assumes "LongestCommonPrefix_precond str1 str2"
  shows
    "LongestCommonPrefix_postcond
      str1 str2 (LongestCommonPrefix str1 str2)"
  sorry

end
