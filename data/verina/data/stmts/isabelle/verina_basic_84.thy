(*
  Statement-only formalization of VERINA corpus artifact verina_basic_84
  (verina__isabelle__verina_basic_84), catalog title "replace": an executable
  integer-array traversal replaces every entry greater than a threshold with
  -1 and preserves every other entry, together with its unconditional
  precondition, postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_84
  imports Main
begin

definition replace_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "replace_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition replace_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "replace_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition replace_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "replace_precond arr k \<longleftrightarrow> True"

definition replace_loop_step ::
    "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      int list" where
  "replace_loop_step oldArr k acc i =
    (if replace_getBang oldArr i > k
     then replace_setBang acc i (-1)
     else acc)"

definition replace_loop ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow>
      int list" where
  "replace_loop oldArr k i acc =
    foldl (replace_loop_step oldArr k) acc [i..<length oldArr]"

definition replace :: "int list \<Rightarrow> int \<Rightarrow> int list" where
  "replace arr k = replace_loop arr k 0 arr"

definition replace_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> bool" where
  "replace_postcond arr k result \<longleftrightarrow>
    length result = length arr \<and>
    (\<forall>i. i < length arr \<longrightarrow>
      (replace_getBang arr i > k \<longrightarrow>
        replace_getBang result i = -1)) \<and>
    (\<forall>i. i < length arr \<longrightarrow>
      (replace_getBang arr i \<le> k \<longrightarrow>
        replace_getBang result i = replace_getBang arr i))"

theorem replace_spec_satisfied:
  fixes arr :: "int list" and k :: int
  assumes "replace_precond arr k"
  shows "replace_postcond arr k (replace arr k)"
  sorry

end
