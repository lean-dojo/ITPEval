(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_26,
  catalog title "letterCombinations": an executable Unicode-scalar string
  program generates telephone-keypad letter combinations, together with its
  precondition and extensional output contract. This file contains no proof.
*)

theory verina_advanced_26
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

definition digitToLetters :: "lean_char \<Rightarrow> lean_char list" where
  "digitToLetters c =
    (if c = ascii 50 then map ascii [97, 98, 99]
     else if c = ascii 51 then map ascii [100, 101, 102]
     else if c = ascii 52 then map ascii [103, 104, 105]
     else if c = ascii 53 then map ascii [106, 107, 108]
     else if c = ascii 54 then map ascii [109, 110, 111]
     else if c = ascii 55 then map ascii [112, 113, 114, 115]
     else if c = ascii 56 then map ascii [116, 117, 118]
     else if c = ascii 57 then map ascii [119, 120, 121, 122]
     else [])"

definition letterCombinations_precond :: "lean_string \<Rightarrow> bool" where
  "letterCombinations_precond digits \<longleftrightarrow> True"

fun letterCombinations_go :: "lean_char list \<Rightarrow> lean_string list" where
  "letterCombinations_go [] = []"
| "letterCombinations_go (d # ds) =
    (let restCombinations = letterCombinations_go ds;
         currentLetters = digitToLetters d
     in case restCombinations of
          [] \<Rightarrow> map (\<lambda>c. [c]) currentLetters
        | _ \<Rightarrow>
            concat
              (map
                (\<lambda>c. map (\<lambda>s. c # s) restCombinations)
                currentLetters))"

definition letterCombinations :: "lean_string \<Rightarrow> lean_string list" where
  "letterCombinations digits =
    (if list_ex (\<lambda>c. digitToLetters c = []) digits
     then []
     else letterCombinations_go digits)"

definition valid_keypad_digit :: "lean_char \<Rightarrow> bool" where
  "valid_keypad_digit c \<longleftrightarrow>
    c \<in> set (map ascii [50, 51, 52, 53, 54, 55, 56, 57])"

definition letterCombinations_expected_step ::
    "lean_string list \<Rightarrow> lean_char list \<Rightarrow> lean_string list" where
  "letterCombinations_expected_step acc ls =
    concat (map (\<lambda>s. map (\<lambda>c. s @ [c]) ls) acc)"

definition letterCombinations_expected ::
    "lean_string \<Rightarrow> lean_string list" where
  "letterCombinations_expected digits =
    foldl letterCombinations_expected_step [[]]
      (map digitToLetters digits)"

definition letterCombinations_postcond ::
    "lean_string \<Rightarrow> lean_string list \<Rightarrow> bool" where
  "letterCombinations_postcond digits result \<longleftrightarrow>
    (if digits = []
     then result = []
     else if list_ex (\<lambda>c. \<not> valid_keypad_digit c) digits
     then result = []
     else
       (let expected = letterCombinations_expected digits
        in length result = length expected \<and>
           list_all (\<lambda>s. s \<in> set expected) result \<and>
           list_all (\<lambda>s. s \<in> set result) expected))"

theorem letterCombinations_spec_satisfied:
  assumes "letterCombinations_precond digits"
  shows
    "letterCombinations_postcond digits (letterCombinations digits)"
  sorry

end
