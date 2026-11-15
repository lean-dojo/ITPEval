(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_69,
  catalog title "searchInsert": an executable linear search returns the first
  index at which a target can occur or be inserted in a strictly increasing
  integer list, together with its precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_advanced_69
  imports Main
begin

fun searchInsert_pairwise_lt :: "int list \<Rightarrow> bool" where
  "searchInsert_pairwise_lt [] = True"
| "searchInsert_pairwise_lt (x # xs) =
    (list_all (\<lambda>y. x < y) xs \<and>
     searchInsert_pairwise_lt xs)"

definition searchInsert_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "searchInsert_precond xs target \<longleftrightarrow>
    searchInsert_pairwise_lt xs"

fun searchInsert_helper ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> nat" where
  "searchInsert_helper [] idx target = idx"
| "searchInsert_helper (y # ys) idx target =
    (if target \<le> y
     then idx
     else searchInsert_helper ys (idx + 1) target)"

definition searchInsert :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "searchInsert xs target =
    (case xs of
       [] \<Rightarrow> 0
     | y # ys \<Rightarrow> searchInsert_helper xs 0 target)"

definition searchInsert_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "searchInsert_postcond xs target result \<longleftrightarrow>
    (let allBeforeLess =
       list_all (\<lambda>i. xs ! i < target) [0..<result];
         inBounds = (result \<le> length xs);
         insertedCorrectly =
           (result < length xs \<longrightarrow> target \<le> xs ! result)
     in inBounds \<and> allBeforeLess \<and> insertedCorrectly)"

theorem searchInsert_spec_satisfied:
  assumes "searchInsert_precond xs target"
  shows
    "searchInsert_postcond
      xs target (searchInsert xs target)"
  sorry

end
