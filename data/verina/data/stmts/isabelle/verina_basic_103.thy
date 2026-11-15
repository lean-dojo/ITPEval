(*
  Statement-only formalization of VERINA corpus artifact verina_basic_103,
  catalog title "UpdateElements": an executable integer-array program
  increases the element at zero-based index 4 by 3, sets index 7 to 516, and
  leaves every other element unchanged under the length-at-least-8
  precondition. This file contains no proof.
*)

theory verina_basic_103
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition intList_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "intList_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition UpdateElements_precond :: "int list \<Rightarrow> bool" where
  "UpdateElements_precond a \<longleftrightarrow> length a \<ge> 8"

definition UpdateElements :: "int list \<Rightarrow> int list" where
  "UpdateElements a =
    (let a1 = intList_setBang a 4 (intList_getBang a 4 + 3);
         a2 = intList_setBang a1 7 516
     in a2)"

definition UpdateElements_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "UpdateElements_postcond a result \<longleftrightarrow>
    length result = length a \<and>
    intList_getBang result 4 = intList_getBang a 4 + 3 \<and>
    intList_getBang result 7 = 516 \<and>
    (\<forall>i<length a.
      i \<noteq> 4 \<longrightarrow>
      i \<noteq> 7 \<longrightarrow>
      intList_getBang result i = intList_getBang a i)"

theorem UpdateElements_spec_satisfied:
  assumes "UpdateElements_precond a"
  shows "UpdateElements_postcond a (UpdateElements a)"
  sorry

end
