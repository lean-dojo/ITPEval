(*
  Statement-only formalization of VERINA corpus artifact verina_basic_57
  (verina__isabelle__verina_basic_57), catalog title "CountLessThan": an
  executable array loop counts the integers strictly below a threshold,
  together with its unconditional precondition, fold-based postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_57
  imports Main
begin

definition CountLessThan_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "CountLessThan_precond numbers threshold \<longleftrightarrow> True"

definition countLessThan_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "countLessThan_getBang numbers i =
    (if i < length numbers then numbers ! i else 0)"

definition countLessThan_loop_step ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "countLessThan_loop_step numbers threshold acc i =
    (if countLessThan_getBang numbers i < threshold
     then acc + 1
     else acc)"

definition countLessThan_loop ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "countLessThan_loop numbers threshold i acc =
    foldl (countLessThan_loop_step numbers threshold)
      acc [i..<length numbers]"

definition countLessThan :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "countLessThan numbers threshold =
    countLessThan_loop numbers threshold 0 0"

definition CountLessThan :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "CountLessThan numbers threshold =
    countLessThan numbers threshold"

definition CountLessThan_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "CountLessThan_postcond numbers threshold result \<longleftrightarrow>
    result -
      foldl
        (\<lambda>count n. if n < threshold then count + 1 else count)
        0 numbers = 0 \<and>
    foldl
      (\<lambda>count n. if n < threshold then count + 1 else count)
      0 numbers - result = 0"

theorem CountLessThan_spec_satisfied:
  assumes "CountLessThan_precond numbers threshold"
  shows
    "CountLessThan_postcond
      numbers threshold (CountLessThan numbers threshold)"
  sorry

end
