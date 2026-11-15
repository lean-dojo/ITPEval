(*
  Statement-only formalization of VERINA corpus artifact verina_basic_21
  (verina__isabelle__verina_basic_21), catalog title "isSublist": an
  executable integer-list search returns true exactly when the first list is
  a contiguous slice of the second, together with its unconditional
  precondition, Boolean postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_21
  imports Main
begin

definition isSublist_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "isSublist_precond sub main \<longleftrightarrow> True"

fun isSublist_check ::
    "nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> bool" where
  "isSublist_check 0 sub main i = False"
| "isSublist_check (Suc fuel) sub main i =
    (let subLen = length sub;
         mainLen = length main
     in if i + subLen > mainLen
        then False
        else if sub = take subLen (drop i main)
        then True
        else if i + 1 \<le> mainLen
        then isSublist_check fuel sub main (i + 1)
        else False)"

definition isSublist :: "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "isSublist sub main =
    (let subLen = length sub;
         mainLen = length main
     in if subLen > mainLen
        then False
        else isSublist_check (Suc mainLen) sub main 0)"

definition isSublist_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool \<Rightarrow> bool" where
  "isSublist_postcond sub main result \<longleftrightarrow>
    ((\<exists>i. i + length sub \<le> length main \<and>
        sub = take (length sub) (drop i main))
      \<longleftrightarrow> result)"

theorem isSublist_spec_satisfied:
  assumes "isSublist_precond sub main"
  shows "isSublist_postcond sub main (isSublist sub main)"
  sorry

end
