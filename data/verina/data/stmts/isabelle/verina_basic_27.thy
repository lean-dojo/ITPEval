(*
  Statement-only formalization of VERINA corpus artifact verina_basic_27
  (verina__isabelle__verina_basic_27), catalog title
  "findFirstRepeatedChar": an executable Unicode-scalar string scan returns
  the first character whose repeated occurrence is encountered, or None when
  all characters are distinct, together with its unconditional precondition,
  second-occurrence postcondition, and final correctness proposition. This
  file contains no proof.
*)

theory verina_basic_27
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

definition findFirstRepeatedChar_precond :: "lean_string \<Rightarrow> bool" where
  "findFirstRepeatedChar_precond s \<longleftrightarrow> True"

definition findFirstRepeatedChar_toList ::
    "lean_string \<Rightarrow> lean_char list" where
  "findFirstRepeatedChar_toList s = s"

fun findFirstRepeatedChar_loop ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> lean_char option" where
  "findFirstRepeatedChar_loop seen [] = None"
| "findFirstRepeatedChar_loop seen (c # cs) =
    (if c \<in> set seen
     then Some c
     else findFirstRepeatedChar_loop (c # seen) cs)"

definition findFirstRepeatedChar ::
    "lean_string \<Rightarrow> lean_char option" where
  "findFirstRepeatedChar s =
    findFirstRepeatedChar_loop [] (findFirstRepeatedChar_toList s)"

fun findFirstRepeatedChar_idxOf ::
    "lean_char list \<Rightarrow> lean_char \<Rightarrow> nat" where
  "findFirstRepeatedChar_idxOf [] c = 0"
| "findFirstRepeatedChar_idxOf (x # xs) c =
    (if x = c
     then 0
     else Suc (findFirstRepeatedChar_idxOf xs c))"

fun findFirstRepeatedChar_findSecondIdxAux ::
    "lean_char list \<Rightarrow> lean_char \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "findFirstRepeatedChar_findSecondIdxAux [] c firstIdx i = i"
| "findFirstRepeatedChar_findSecondIdxAux (x # xs) c firstIdx i =
    (if x = c \<and> i \<noteq> firstIdx
     then i
     else
       findFirstRepeatedChar_findSecondIdxAux
         xs c firstIdx (Suc i))"

definition findFirstRepeatedChar_secondIdx ::
    "lean_char list \<Rightarrow> lean_char \<Rightarrow> nat" where
  "findFirstRepeatedChar_secondIdx cs c =
    findFirstRepeatedChar_findSecondIdxAux
      cs c (findFirstRepeatedChar_idxOf cs c) 0"

definition findFirstRepeatedChar_postcond ::
    "lean_string \<Rightarrow> lean_char option \<Rightarrow> bool" where
  "findFirstRepeatedChar_postcond s result \<longleftrightarrow>
    (let cs = findFirstRepeatedChar_toList s
     in case result of
          None \<Rightarrow> distinct cs
        | Some c \<Rightarrow>
            (let secondIdx = findFirstRepeatedChar_secondIdx cs c
             in 2 \<le> count_list cs c \<and>
                distinct (take secondIdx cs)))"

theorem findFirstRepeatedChar_spec_satisfied:
  assumes "findFirstRepeatedChar_precond s"
  shows
    "findFirstRepeatedChar_postcond s (findFirstRepeatedChar s)"
  sorry

end
