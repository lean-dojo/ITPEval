(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_56,
  catalog title "moveZeroes": filtering partitions an integer list into its
  nonzero entries followed by its zero entries, with a correctness contract
  preserving nonzero order, trailing zeroes, zero count, and length. This file
  contains no proof.
*)

theory verina_advanced_56
  imports Main
begin

definition moveZeroes_precond :: "int list \<Rightarrow> bool" where
  "moveZeroes_precond xs \<longleftrightarrow> True"

definition moveZeroes :: "int list \<Rightarrow> int list" where
  "moveZeroes xs =
    filter (\<lambda>x. x \<noteq> 0) xs @ filter (\<lambda>x. x = 0) xs"

fun countVal :: "int \<Rightarrow> int list \<Rightarrow> nat" where
  "countVal val [] = 0"
| "countVal val (x # xs) =
    (let rest = countVal val xs
     in if x = val then rest + 1 else rest)"

fun isSubsequence :: "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "isSubsequence [] ys = True"
| "isSubsequence (x # xs) [] = False"
| "isSubsequence (x # xs) (y # ys) =
    (if x = y
     then isSubsequence xs ys
     else isSubsequence (x # xs) ys)"

definition moveZeroes_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "moveZeroes_postcond xs result \<longleftrightarrow>
    isSubsequence (filter (\<lambda>x. x \<noteq> 0) xs) result \<and>
    list_all
      (\<lambda>x. x = 0)
      (dropWhile (\<lambda>x. x \<noteq> 0) result) \<and>
    countVal 0 xs = countVal 0 result \<and>
    length xs = length result"

theorem moveZeroes_spec_satisfied:
  assumes "moveZeroes_precond xs"
  shows "moveZeroes_postcond xs (moveZeroes xs)"
  sorry

end
