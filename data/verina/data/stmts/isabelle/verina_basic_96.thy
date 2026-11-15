(*
  Statement-only formalization of VERINA corpus artifact verina_basic_96
  (verina__isabelle__verina_basic_96), catalog title "SwapSimultaneous": a
  total executable integer program returns its two inputs in reversed order
  as a pair, together with its unconditional precondition, component-wise
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_96
  imports Main
begin

definition SwapSimultaneous_precond ::
    "int \<Rightarrow> int \<Rightarrow> bool" where
  "SwapSimultaneous_precond X Y \<longleftrightarrow> True"

definition SwapSimultaneous ::
    "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "SwapSimultaneous X Y = (Y, X)"

definition SwapSimultaneous_postcond ::
    "int \<Rightarrow> int \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "SwapSimultaneous_postcond X Y result \<longleftrightarrow>
    fst result = Y \<and>
    snd result = X \<and>
    (X \<noteq> Y \<longrightarrow>
      fst result \<noteq> X \<and> snd result \<noteq> Y)"

theorem SwapSimultaneous_spec_satisfied:
  fixes X Y :: int
  assumes "SwapSimultaneous_precond X Y"
  shows "SwapSimultaneous_postcond X Y (SwapSimultaneous X Y)"
  sorry

end
