(*
  Statement-only formalization of VERINA corpus artifact verina_basic_64
  (verina__isabelle__verina_basic_64), catalog title "insert": an executable
  Unicode-character array program inserts the first p characters of one array
  into the first l characters of another at atPos, together with its bounds
  precondition, segment-wise postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_64
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

type_synonym lean_char_array = "lean_char list"

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

definition lean_nul :: lean_char where
  "lean_nul =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False False False False False False False)"

definition lean_space :: lean_char where
  "lean_space =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True False False False False False)"

definition lean_char_array_getBang ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char" where
  "lean_char_array_getBang xs i =
    (if i < length xs then xs ! i else lean_nul)"

definition lean_char_array_setBang ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char \<Rightarrow>
      lean_char_array" where
  "lean_char_array_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition insert_precond ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char_array \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> bool" where
  "insert_precond oline l nl p atPos \<longleftrightarrow>
    l \<le> length oline \<and>
    p \<le> length nl \<and>
    atPos \<le> l"

definition insert_prefix_step ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char_array \<Rightarrow>
      nat \<Rightarrow> lean_char_array" where
  "insert_prefix_step oline atPos acc i =
    (if i < atPos
     then lean_char_array_setBang acc i
       (lean_char_array_getBang oline i)
     else acc)"

definition insert_new_step ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char_array \<Rightarrow>
      nat \<Rightarrow> lean_char_array" where
  "insert_new_step nl atPos acc i =
    lean_char_array_setBang acc (atPos + i)
      (lean_char_array_getBang nl i)"

definition insert_suffix_step ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char_array" where
  "insert_suffix_step oline p atPos acc i =
    (if atPos \<le> i
     then lean_char_array_setBang acc (i + p)
       (lean_char_array_getBang oline i)
     else acc)"

definition insert ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char_array \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> lean_char_array" where
  "insert oline l nl p atPos =
    (let result0 = replicate (l + p) lean_space;
         result1 =
           foldl (insert_prefix_step oline atPos) result0 [0..<l];
         result2 =
           foldl (insert_new_step nl atPos) result1 [0..<p];
         result3 =
           foldl (insert_suffix_step oline p atPos) result2 [0..<l]
     in result3)"

definition insert_postcond ::
    "lean_char_array \<Rightarrow> nat \<Rightarrow> lean_char_array \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> lean_char_array \<Rightarrow> bool" where
  "insert_postcond oline l nl p atPos result \<longleftrightarrow>
    length result = l + p \<and>
    list_all
      (\<lambda>i. lean_char_array_getBang result (atPos + i) =
        lean_char_array_getBang nl i)
      [0..<p] \<and>
    list_all
      (\<lambda>i. lean_char_array_getBang result i =
        lean_char_array_getBang oline i)
      [0..<atPos] \<and>
    list_all
      (\<lambda>i. lean_char_array_getBang result (atPos + p + i) =
        lean_char_array_getBang oline (atPos + i))
      [0..<l - atPos]"

theorem insert_spec_satisfied:
  assumes "insert_precond oline l nl p atPos"
  shows
    "insert_postcond
      oline l nl p atPos (insert oline l nl p atPos)"
  sorry

end
