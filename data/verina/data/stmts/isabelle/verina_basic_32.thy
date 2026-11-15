(*
  Statement-only formalization of VERINA corpus artifact verina_basic_32,
  catalog title "swapFirstAndLast": an executable integer-array program swaps
  the first and last elements of a nonempty array while leaving the intervening
  elements unchanged. This file contains no proof.
*)

theory verina_basic_32
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition intList_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "intList_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition swapFirstAndLast_precond :: "int list \<Rightarrow> bool" where
  "swapFirstAndLast_precond a \<longleftrightarrow> length a > 0"

definition swapFirstAndLast :: "int list \<Rightarrow> int list" where
  "swapFirstAndLast a =
    (let first = intList_getBang a 0;
         last = intList_getBang a (length a - 1)
     in intList_setBang
          (intList_setBang a 0 last)
          (length a - 1)
          first)"

definition swapFirstAndLast_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "swapFirstAndLast_postcond a result \<longleftrightarrow>
    length result = length a \<and>
    intList_getBang result 0 =
      intList_getBang a (length a - 1) \<and>
    intList_getBang result (length result - 1) =
      intList_getBang a 0 \<and>
    list_all
      (\<lambda>i.
        intList_getBang result (i + 1) =
          intList_getBang a (i + 1))
      [0..<length result - 2]"

theorem swapFirstAndLast_spec_satisfied:
  assumes "swapFirstAndLast_precond a"
  shows "swapFirstAndLast_postcond a (swapFirstAndLast a)"
  sorry

end
