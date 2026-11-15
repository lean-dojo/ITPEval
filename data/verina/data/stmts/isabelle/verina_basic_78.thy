(*
  Statement-only formalization of VERINA corpus artifact verina_basic_78
  (verina__isabelle__verina_basic_78), catalog title "MultipleReturns": a
  total executable integer program returns the sum and difference of two
  inputs as a pair, together with its unconditional precondition,
  component-wise postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_78
  imports Main
begin

definition MultipleReturns_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "MultipleReturns_precond x y \<longleftrightarrow> True"

definition MultipleReturns :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "MultipleReturns x y =
    (let more = x + y;
         less = x - y
     in (more, less))"

definition MultipleReturns_postcond ::
    "int \<Rightarrow> int \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "MultipleReturns_postcond x y result \<longleftrightarrow>
    fst result = x + y \<and>
    snd result + y = x"

theorem MultipleReturns_spec_satisfied:
  assumes "MultipleReturns_precond x y"
  shows "MultipleReturns_postcond x y (MultipleReturns x y)"
  sorry

end
