(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_71,
  catalog title "shortestBeautifulSubstring": an executable Unicode-scalar
  string program enumerates nonempty contiguous substrings and selects the
  shortest one containing exactly k ones, breaking length ties
  lexicographically, together with its binary-input precondition, postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_advanced_71
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

definition lean_zero :: lean_char where
  "lean_zero =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True True False False False False)"

definition lean_one :: lean_char where
  "lean_one =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True True False False False True)"

fun lean_string_lt :: "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "lean_string_lt [] [] = False"
| "lean_string_lt [] (y # ys) = True"
| "lean_string_lt (x # xs) [] = False"
| "lean_string_lt (x # xs) (y # ys) =
    (lean_char_to_nat x < lean_char_to_nat y \<or>
     (x = y \<and> lean_string_lt xs ys))"

definition lean_string_le :: "lean_string \<Rightarrow> lean_string \<Rightarrow> bool"
  where
  "lean_string_le a b \<longleftrightarrow> \<not> lean_string_lt b a"

definition countOnes :: "lean_char list \<Rightarrow> nat" where
  "countOnes lst =
    foldl (\<lambda>acc c. if c = lean_one then acc + 1 else acc) 0 lst"

definition shortestBeautifulSubstring_precond ::
    "lean_string \<Rightarrow> nat \<Rightarrow> bool" where
  "shortestBeautifulSubstring_precond s k \<longleftrightarrow>
    list_all (\<lambda>c. c = lean_zero \<or> c = lean_one) s"

definition listToString :: "lean_char list \<Rightarrow> lean_string" where
  "listToString lst = lst"

definition isLexSmaller ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> bool" where
  "isLexSmaller a b \<longleftrightarrow>
    lean_string_lt (listToString a) (listToString b)"

definition allSubstrings ::
    "lean_char list \<Rightarrow> lean_char list list" where
  "allSubstrings s =
    (let n = length s
     in concat
       (map
         (\<lambda>i.
           map (\<lambda>j. take (j + 1) (drop i s)) [0..<n - i])
         [0..<n]))"

definition shortestBeautifulSubstring_compare ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> bool" where
  "shortestBeautifulSubstring_compare a b \<longleftrightarrow>
    length a < length b \<or>
    (length a = length b \<and> isLexSmaller a b)"

fun shortestBeautifulSubstring_select ::
    "lean_char list option \<Rightarrow>
     lean_char list \<Rightarrow>
     lean_char list option" where
  "shortestBeautifulSubstring_select None cur = Some cur"
| "shortestBeautifulSubstring_select (Some best) cur =
    (if shortestBeautifulSubstring_compare cur best
     then Some cur
     else Some best)"

definition shortestBeautifulSubstring ::
    "lean_string \<Rightarrow> nat \<Rightarrow> lean_string" where
  "shortestBeautifulSubstring s k =
    (let chars = s;
         candidates =
           filter (\<lambda>sub. countOnes sub = k) (allSubstrings chars);
         best = foldl shortestBeautifulSubstring_select None candidates
     in case best of
          Some b \<Rightarrow> listToString b
        | None \<Rightarrow> [])"

definition shortestBeautifulSubstring_post_substrings ::
    "lean_string \<Rightarrow> lean_char list list" where
  "shortestBeautifulSubstring_post_substrings s =
    (let chars = s
     in concat
       (map
         (\<lambda>i.
           map
             (\<lambda>len. take len (drop i chars))
             [0..<length chars - i + 1])
         [0..<length chars]))"

definition shortestBeautifulSubstring_targets ::
    "lean_string \<Rightarrow> nat \<Rightarrow> lean_string list" where
  "shortestBeautifulSubstring_targets s k =
    (let substrings = shortestBeautifulSubstring_post_substrings s;
         beautiful = filter (\<lambda>sub. countOnes sub = k) substrings
     in filter (\<lambda>target. target \<noteq> [])
          (map listToString beautiful))"

definition shortestBeautifulSubstring_postcond ::
    "lean_string \<Rightarrow> nat \<Rightarrow> lean_string \<Rightarrow> bool" where
  "shortestBeautifulSubstring_postcond s k result \<longleftrightarrow>
    (let targets = shortestBeautifulSubstring_targets s k
     in (result = [] \<and> targets = []) \<or>
        (result \<in> set targets \<and>
         (\<forall>r \<in> set targets.
           length r > length result \<or>
           (length r = length result \<and>
            lean_string_le result r))))"

theorem shortestBeautifulSubstring_spec_satisfied:
  assumes "shortestBeautifulSubstring_precond s k"
  shows
    "shortestBeautifulSubstring_postcond
      s k (shortestBeautifulSubstring s k)"
  sorry

end
