(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_27,
  catalog title "longestCommonSubsequence": an executable Unicode-scalar
  string program computes a longest common subsequence using its recursive
  left-biased tie-breaking algorithm, together with its precondition and
  exhaustive subsequence-maximality postcondition. This file contains no proof.
*)

theory verina_advanced_27
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

definition longestCommonSubsequence_precond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> bool" where
  "longestCommonSubsequence_precond s1 s2 \<longleftrightarrow> True"

definition toCharList :: "lean_string \<Rightarrow> lean_char list" where
  "toCharList s = s"

definition fromCharList :: "lean_char list \<Rightarrow> lean_string" where
  "fromCharList cs = foldl (\<lambda>acc c. acc @ [c]) [] cs"

fun lcsAux ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> lean_char list" where
  "lcsAux [] ys = []"
| "lcsAux (x # xs) [] = []"
| "lcsAux (x # xs) (y # ys) =
    (if x = y
     then x # lcsAux xs ys
     else
       (let left = lcsAux xs (y # ys);
            right = lcsAux (x # xs) ys
        in if length left \<ge> length right then left else right))"

definition longestCommonSubsequence ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> lean_string" where
  "longestCommonSubsequence s1 s2 =
    (let xs = toCharList s1;
         ys = toCharList s2;
         resultList = lcsAux xs ys
     in fromCharList resultList)"

definition allSubseq :: "lean_char list \<Rightarrow> lean_char list list" where
  "allSubseq arr =
    map rev
      (foldl
        (\<lambda>acc x. acc @ map (\<lambda>sub. x # sub) acc)
        [[]] arr)"

definition longestCommonSubsequence_postcond ::
    "lean_string \<Rightarrow> lean_string \<Rightarrow> lean_string \<Rightarrow> bool"
  where
  "longestCommonSubsequence_postcond s1 s2 result \<longleftrightarrow>
    (let subseqA = allSubseq s1;
         subseqB = allSubseq s2;
         commonSubseq =
           filter (\<lambda>l. l \<in> set subseqB) subseqA
     in result \<in> set commonSubseq \<and>
        list_all (\<lambda>l. length l \<le> length result) commonSubseq)"

theorem longestCommonSubsequence_spec_satisfied:
  assumes "longestCommonSubsequence_precond s1 s2"
  shows
    "longestCommonSubsequence_postcond
      s1 s2 (longestCommonSubsequence s1 s2)"
  sorry

end
