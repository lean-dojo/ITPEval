(*
  Statement-only formalization of VERINA corpus artifact verina_basic_62
  (verina__isabelle__verina_basic_62), catalog title "Find": an executable
  left-to-right search of an integer array returns the first index containing
  the key, or -1 when the key is absent, together with its unconditional
  precondition, exact first-occurrence postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_62
  imports Main
begin

definition Find_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "Find_getBang a i =
    (if i < length a then a ! i else 0)"

definition Find_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "Find_precond a key \<longleftrightarrow> True"

fun Find_search ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" where
  "Find_search [] key index = -1"
| "Find_search (x # xs) key index =
    (if x = key
     then int index
     else Find_search xs key (Suc index))"

definition Find :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "Find a key = Find_search a key 0"

definition Find_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "Find_postcond a key result \<longleftrightarrow>
    (result = -1 \<or>
      (result \<ge> 0 \<and> result < int (length a))) \<and>
    (result \<noteq> -1 \<longrightarrow>
      Find_getBang a (nat result) = key \<and>
      (\<forall>i. i < nat result \<longrightarrow>
        Find_getBang a i \<noteq> key)) \<and>
    (result = -1 \<longrightarrow>
      (\<forall>i. i < length a \<longrightarrow>
        Find_getBang a i \<noteq> key))"

theorem Find_spec_satisfied:
  assumes "Find_precond a key"
  shows "Find_postcond a key (Find a key)"
  sorry

end
