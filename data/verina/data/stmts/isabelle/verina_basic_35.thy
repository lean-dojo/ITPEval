(*
  Statement-only formalization of VERINA corpus artifact verina_basic_35
  (verina__isabelle__verina_basic_35), catalog title "MoveZeroesToEnd": an
  executable integer-array program stably partitions the entries into the
  nonzero entries followed by the zero entries, together with its unconditional
  precondition, permutation and first-zero split postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_35
  imports Main
begin

definition MoveZeroesToEnd_precond :: "int list \<Rightarrow> bool" where
  "MoveZeroesToEnd_precond arr \<longleftrightarrow> True"

definition MoveZeroesToEnd :: "int list \<Rightarrow> int list" where
  "MoveZeroesToEnd arr =
    filter (\<lambda>x. x \<noteq> 0) arr @ filter (\<lambda>x. x = 0) arr"

fun MoveZeroesToEnd_idxOf :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "MoveZeroesToEnd_idxOf [] value = 0"
| "MoveZeroesToEnd_idxOf (x # xs) value =
    (if x = value then 0 else Suc (MoveZeroesToEnd_idxOf xs value))"

definition MoveZeroesToEnd_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "MoveZeroesToEnd_postcond arr result \<longleftrightarrow>
    (let firstResZeroIdx = MoveZeroesToEnd_idxOf result 0
     in (\<forall>value. count_list result value = count_list arr value) \<and>
        take firstResZeroIdx result =
          filter (\<lambda>x. x \<noteq> 0) arr \<and>
        drop firstResZeroIdx result =
          filter (\<lambda>x. x = 0) arr)"

theorem MoveZeroesToEnd_spec_satisfied:
  assumes "MoveZeroesToEnd_precond arr"
  shows
    "MoveZeroesToEnd_postcond arr (MoveZeroesToEnd arr)"
  sorry

end
