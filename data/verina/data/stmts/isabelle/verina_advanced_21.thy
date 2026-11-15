(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_21,
  catalog title "isPalindrome": an executable Unicode-scalar string program
  checks matching characters from both ends and independently compares the
  string with its accumulator-built reversal, together with its precondition
  and Boolean palindrome contract. This file contains no proof.
*)

theory verina_advanced_21
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

definition isPalindrome_precond :: "lean_string \<Rightarrow> bool" where
  "isPalindrome_precond s \<longleftrightarrow> True"

fun lean_list_get_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "lean_list_get_opt [] i = None"
| "lean_list_get_opt (x # xs) 0 = Some x"
| "lean_list_get_opt (x # xs) (Suc i) = lean_list_get_opt xs i"

fun checkIndices_go ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lean_char list \<Rightarrow> bool" where
  "checkIndices_go 0 left right chars = False"
| "checkIndices_go (Suc fuel) left right chars =
    (if left \<ge> right
     then True
     else
       (case (lean_list_get_opt chars left, lean_list_get_opt chars right) of
          (Some cLeft, Some cRight) \<Rightarrow>
            (if cLeft = cRight
             then checkIndices_go fuel (left + 1) (right - 1) chars
             else False)
        | _ \<Rightarrow> False))"

definition checkIndices ::
    "nat \<Rightarrow> nat \<Rightarrow> lean_char list \<Rightarrow> bool" where
  "checkIndices left right chars =
    checkIndices_go (Suc (length chars)) left right chars"

fun reverseList ::
    "lean_char list \<Rightarrow> lean_char list \<Rightarrow> lean_char list" where
  "reverseList acc [] = acc"
| "reverseList acc (x # xs) = reverseList (x # acc) xs"

definition isPalindrome :: "lean_string \<Rightarrow> bool" where
  "isPalindrome s =
    (let len = length s
     in if len \<le> 1
        then True
        else
          (let arr = s;
               approach1 = checkIndices 0 (len - 1) arr;
               reversed = reverseList [] arr;
               approach2 = (arr = reversed)
           in approach1 \<and> approach2))"

definition isPalindrome_postcond ::
    "lean_string \<Rightarrow> bool \<Rightarrow> bool" where
  "isPalindrome_postcond s result \<longleftrightarrow>
    (result \<longrightarrow> s = rev s) \<and>
    (\<not> result \<longrightarrow> s \<noteq> [] \<and> s \<noteq> rev s)"

theorem isPalindrome_spec_satisfied:
  assumes "isPalindrome_precond s"
  shows "isPalindrome_postcond s (isPalindrome s)"
  sorry

end
