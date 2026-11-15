(*
  Statement-only formalization of VERINA corpus artifact verina_basic_13,
  catalog title "cubeElements": an executable integer-array program maps each
  input element to its cube, together with its trivial precondition, same-size
  pointwise cube postcondition, and correctness contract. This file contains
  no proof.
*)

theory verina_basic_13
  imports Main
begin

definition cubeElements_precond :: "int list \<Rightarrow> bool" where
  "cubeElements_precond a \<longleftrightarrow> True"

definition cubeElements :: "int list \<Rightarrow> int list" where
  "cubeElements a = map (\<lambda>x. x * x * x) a"

definition cubeElements_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "cubeElements_postcond a result \<longleftrightarrow>
    length result = length a \<and>
    (\<forall>i<length a. result ! i = a ! i * a ! i * a ! i)"

theorem cubeElements_spec_satisfied:
  assumes "cubeElements_precond a"
  shows "cubeElements_postcond a (cubeElements a)"
  sorry

end
