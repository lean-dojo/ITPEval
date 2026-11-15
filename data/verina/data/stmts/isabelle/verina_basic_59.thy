(*
  Statement-only formalization of VERINA corpus artifact verina_basic_59
  (verina__isabelle__verina_basic_59), catalog title "DoubleQuadruple": a
  total executable integer program returns twice its input and then twice
  that value as a pair, together with its unconditional precondition,
  component-wise postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_59
  imports Main
begin

definition DoubleQuadruple_precond :: "int \<Rightarrow> bool" where
  "DoubleQuadruple_precond x \<longleftrightarrow> True"

definition DoubleQuadruple :: "int \<Rightarrow> int \<times> int" where
  "DoubleQuadruple x =
    (let a = 2 * x;
         b = 2 * a
     in (a, b))"

definition DoubleQuadruple_postcond ::
    "int \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "DoubleQuadruple_postcond x result \<longleftrightarrow>
    fst result = 2 * x \<and>
    snd result = 2 * fst result"

theorem DoubleQuadruple_spec_satisfied:
  assumes "DoubleQuadruple_precond x"
  shows
    "DoubleQuadruple_postcond x (DoubleQuadruple x)"
  sorry

end
