(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_36,
  catalog title "majorityElement": an executable candidate-cancellation
  program returns a natural number occurring strictly more than half the
  input-list length when such an element exists, together with its
  correctness contract. This file contains no proof.
*)

theory verina_advanced_36
  imports Main
begin

definition majorityElement_precond :: "nat list \<Rightarrow> bool" where
  "majorityElement_precond xs \<longleftrightarrow>
    length xs > 0 \<and>
    list_ex
      (\<lambda>x. count_list xs x > length xs div 2)
      xs"

fun majorityElement_countOccurrences ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "majorityElement_countOccurrences target [] = 0"
| "majorityElement_countOccurrences target (y # ys) =
    (if y = target
     then 1 + majorityElement_countOccurrences target ys
     else majorityElement_countOccurrences target ys)"

fun majorityElement_findCandidate ::
    "nat list \<Rightarrow> nat option \<Rightarrow> nat \<Rightarrow> nat" where
  "majorityElement_findCandidate [] candidate count =
    (case candidate of Some c \<Rightarrow> c | None \<Rightarrow> 0)"
| "majorityElement_findCandidate (x # xs) candidate count =
    (case candidate of
       Some c \<Rightarrow>
         (if x = c
          then majorityElement_findCandidate xs (Some c) (count + 1)
          else if count = 0
               then majorityElement_findCandidate xs (Some x) 1
               else majorityElement_findCandidate xs (Some c) (count - 1))
     | None \<Rightarrow> majorityElement_findCandidate xs (Some x) 1)"

definition majorityElement :: "nat list \<Rightarrow> nat" where
  "majorityElement xs = majorityElement_findCandidate xs None 0"

definition majorityElement_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "majorityElement_postcond xs result \<longleftrightarrow>
    (let count = count_list xs result
     in count > length xs div 2)"

theorem majorityElement_spec_satisfied:
  assumes "majorityElement_precond xs"
  shows "majorityElement_postcond xs (majorityElement xs)"
  sorry

end
