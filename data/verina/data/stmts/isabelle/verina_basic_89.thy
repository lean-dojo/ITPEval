(*
  Statement-only formalization of VERINA corpus artifact verina_basic_89
  (verina__isabelle__verina_basic_89), catalog title "SetToSeq": an executable
  left fold removes duplicate integers while preserving first-occurrence
  order, together with its unconditional precondition, membership, uniqueness,
  and order postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_89
  imports Main
begin

definition SetToSeq_precond :: "int list \<Rightarrow> bool" where
  "SetToSeq_precond s \<longleftrightarrow> True"

definition SetToSeq :: "int list \<Rightarrow> int list" where
  "SetToSeq s =
    foldl
      (\<lambda>acc x. if x \<in> set acc then acc else acc @ [x])
      []
      s"

fun SetToSeq_idxOf :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "SetToSeq_idxOf [] x = 0"
| "SetToSeq_idxOf (y # ys) x =
    (if y = x then 0 else Suc (SetToSeq_idxOf ys x))"

fun SetToSeq_pairwise ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "SetToSeq_pairwise relation [] = True"
| "SetToSeq_pairwise relation (x # xs) =
    (list_all (relation x) xs \<and> SetToSeq_pairwise relation xs)"

definition SetToSeq_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "SetToSeq_postcond s result \<longleftrightarrow>
    list_all (\<lambda>a. a \<in> set s) result \<and>
    list_all (\<lambda>a. a \<in> set result) s \<and>
    list_all (\<lambda>a. count_list result a = 1) result \<and>
    SetToSeq_pairwise
      (\<lambda>a b.
        SetToSeq_idxOf result a < SetToSeq_idxOf result b \<longrightarrow>
        SetToSeq_idxOf s a < SetToSeq_idxOf s b)
      result"

theorem SetToSeq_spec_satisfied:
  fixes s :: "int list"
  assumes "SetToSeq_precond s"
  shows "SetToSeq_postcond s (SetToSeq s)"
  sorry

end
