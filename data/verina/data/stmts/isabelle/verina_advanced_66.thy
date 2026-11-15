(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_66,
  catalog title "reverseWords": an executable Unicode-scalar string program
  splits on ASCII spaces, removes empty fields, reverses the words, and joins
  them with single spaces, together with its precondition, postcondition, and
  correctness contract. This file contains no proof.
*)

theory verina_advanced_66
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

definition lean_space :: lean_char where
  "lean_space =
    BMP_Low Trit0 Trit0 Trit0
      (LeanBits3 False False False)
      (LeanByte False False True False False False False False)"

definition reverseWords_precond :: "lean_string \<Rightarrow> bool" where
  "reverseWords_precond words_str \<longleftrightarrow> True"

fun reverseWords_splitOnSpace_go ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> lean_string list" where
  "reverseWords_splitOnSpace_go current [] = [rev current]"
| "reverseWords_splitOnSpace_go current (c # cs) =
    (if c = lean_space
     then rev current # reverseWords_splitOnSpace_go [] cs
     else reverseWords_splitOnSpace_go (c # current) cs)"

definition reverseWords_splitOnSpace ::
    "lean_string \<Rightarrow> lean_string list" where
  "reverseWords_splitOnSpace words_str =
    reverseWords_splitOnSpace_go [] words_str"

fun reverseWords_filterNonEmpty ::
    "lean_string list \<Rightarrow> lean_string list" where
  "reverseWords_filterNonEmpty [] = []"
| "reverseWords_filterNonEmpty (h # t) =
    (if h = []
     then reverseWords_filterNonEmpty t
     else h # reverseWords_filterNonEmpty t)"

fun reverseWords_joinWithSpace ::
    "lean_string list \<Rightarrow> lean_string" where
  "reverseWords_joinWithSpace [] = []"
| "reverseWords_joinWithSpace [w] = w"
| "reverseWords_joinWithSpace (h # w # t) =
    h @ [lean_space] @ reverseWords_joinWithSpace (w # t)"

fun reverseWords_intercalateSpace ::
    "lean_string list \<Rightarrow> lean_string" where
  "reverseWords_intercalateSpace [] = []"
| "reverseWords_intercalateSpace [w] = w"
| "reverseWords_intercalateSpace (h # w # t) =
    h @ [lean_space] @ reverseWords_intercalateSpace (w # t)"

definition reverseWords :: "lean_string \<Rightarrow> lean_string" where
  "reverseWords words_str =
    (let rawWords = reverseWords_splitOnSpace words_str;
         filteredWords = reverseWords_filterNonEmpty rawWords;
         revWords = rev filteredWords;
         result = reverseWords_joinWithSpace revWords
     in result)"

definition reverseWords_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "reverseWords_postcond words_str result \<longleftrightarrow>
    (\<exists>words.
      words =
        filter (\<lambda>w. w \<noteq> []) (reverseWords_splitOnSpace words_str) \<and>
      result = reverseWords_intercalateSpace (rev words))"

theorem reverseWords_spec_satisfied:
  assumes "reverseWords_precond words_str"
  shows "reverseWords_postcond words_str (reverseWords words_str)"
  sorry

end
