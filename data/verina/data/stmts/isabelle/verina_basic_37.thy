(*
  Statement-only formalization of VERINA corpus artifact verina_basic_37
  (verina__isabelle__verina_basic_37), catalog title
  "findFirstOccurrence": an executable left-to-right scan of a pairwise
  nondecreasing integer array returns the first target index, or -1 when the
  target is absent, together with its precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_37
  imports Main
begin

definition findFirstOccurrence_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "findFirstOccurrence_getBang arr i =
    (if i < length arr then arr ! i else 0)"

fun findFirstOccurrence_pairwise_le :: "int list \<Rightarrow> bool" where
  "findFirstOccurrence_pairwise_le [] = True"
| "findFirstOccurrence_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     findFirstOccurrence_pairwise_le xs)"

definition findFirstOccurrence_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "findFirstOccurrence_precond arr target \<longleftrightarrow>
    findFirstOccurrence_pairwise_le arr"

fun findFirstOccurrence_loop ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "findFirstOccurrence_loop [] target i = -1"
| "findFirstOccurrence_loop (a # rest) target i =
    (if a = target
     then int i
     else if a > target
          then -1
          else findFirstOccurrence_loop rest target (i + 1))"

definition findFirstOccurrence ::
    "int list \<Rightarrow> int \<Rightarrow> int" where
  "findFirstOccurrence arr target =
    findFirstOccurrence_loop arr target 0"

definition findFirstOccurrence_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "findFirstOccurrence_postcond arr target result \<longleftrightarrow>
    (result = -1 \<or> result \<ge> 0) \<and>
    (result \<ge> 0 \<longrightarrow>
      nat result < length arr \<and>
      findFirstOccurrence_getBang arr (nat result) = target \<and>
      (\<forall>i<nat result.
        findFirstOccurrence_getBang arr i \<noteq> target)) \<and>
    (result = -1 \<longrightarrow>
      (\<forall>i<length arr.
        findFirstOccurrence_getBang arr i \<noteq> target))"

theorem findFirstOccurrence_spec_satisfied:
  assumes "findFirstOccurrence_precond arr target"
  shows
    "findFirstOccurrence_postcond
      arr target (findFirstOccurrence arr target)"
  sorry

end
