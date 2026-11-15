(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_12,
  catalog title "firstDuplicate": an executable list program returns the first
  integer whose repeated occurrence is encountered when scanning left to
  right, or None for a duplicate-free list, together with its correctness
  contract. This file contains no proof.
*)

theory verina_advanced_12
  imports Main
begin

definition firstDuplicate_precond :: "int list \<Rightarrow> bool" where
  "firstDuplicate_precond lst \<longleftrightarrow> True"

fun firstDuplicate_helper ::
    "int list \<Rightarrow> int list \<Rightarrow> int option" where
  "firstDuplicate_helper seen [] = None"
| "firstDuplicate_helper seen (x # xs) =
    (if x \<in> set seen
     then Some x
     else firstDuplicate_helper (x # seen) xs)"

definition firstDuplicate :: "int list \<Rightarrow> int option" where
  "firstDuplicate lst = firstDuplicate_helper [] lst"

fun firstDuplicate_idxOf :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "firstDuplicate_idxOf [] v = 0"
| "firstDuplicate_idxOf (x # xs) v =
    (if x = v then 0 else Suc (firstDuplicate_idxOf xs v))"

definition secondOccIdx :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "secondOccIdx lst v =
    (let first = firstDuplicate_idxOf lst v
     in first + 1 + firstDuplicate_idxOf (drop (first + 1) lst) v)"

definition firstDuplicate_postcond ::
    "int list \<Rightarrow> int option \<Rightarrow> bool" where
  "firstDuplicate_postcond lst result \<longleftrightarrow>
    (case result of
       None \<Rightarrow> distinct lst
     | Some x \<Rightarrow>
         count_list lst x > 1 \<and>
         list_all
           (\<lambda>y. count_list lst y = 1 \<or>
             secondOccIdx lst x \<le> secondOccIdx lst y)
           lst)"

theorem firstDuplicate_spec_satisfied:
  assumes "firstDuplicate_precond lst"
  shows "firstDuplicate_postcond lst (firstDuplicate lst)"
  sorry

end
