(*
  Statement-only formalization of VERINA corpus artifact verina_basic_67
  (verina__isabelle__verina_basic_67), catalog title "IsPalindrome": an
  executable Unicode-scalar character-list program compares characters from
  both ends and returns true exactly when every mirrored pair is equal,
  together with its unconditional precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_67
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

definition IsPalindrome_precond :: "lean_char list \<Rightarrow> bool" where
  "IsPalindrome_precond x \<longleftrightarrow> True"

fun lean_list_get_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "lean_list_get_opt [] i = None"
| "lean_list_get_opt (x # xs) 0 = Some x"
| "lean_list_get_opt (x # xs) (Suc i) = lean_list_get_opt xs i"

fun isPalindromeHelper ::
    "lean_char list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "isPalindromeHelper x i 0 = True"
| "isPalindromeHelper x i (Suc j) =
    (if i < Suc j
     then
       (case (lean_list_get_opt x i, lean_list_get_opt x (Suc j)) of
          (Some ci, Some cj) \<Rightarrow>
            (if ci \<noteq> cj
             then False
             else isPalindromeHelper x (i + 1) j)
        | _ \<Rightarrow> False)
     else True)"

definition IsPalindrome :: "lean_char list \<Rightarrow> bool" where
  "IsPalindrome x =
    (if length x = 0
     then True
     else isPalindromeHelper x 0 (length x - 1))"

definition IsPalindrome_postcond ::
    "lean_char list \<Rightarrow> bool \<Rightarrow> bool" where
  "IsPalindrome_postcond x result \<longleftrightarrow>
    (result = True \<longleftrightarrow>
      (\<forall>i. i < length x \<longrightarrow>
        x ! i = x ! ((length x - i) - 1)))"

theorem IsPalindrome_spec_satisfied:
  assumes "IsPalindrome_precond x"
  shows "IsPalindrome_postcond x (IsPalindrome x)"
  sorry

end
