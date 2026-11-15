(*
  Statement-only formalization of VERINA corpus artifact verina_basic_91
  (verina__isabelle__verina_basic_91), catalog title "Swap": a total
  executable integer program exchanges two local values and returns them as
  a pair, together with its unconditional precondition, component-wise
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_91
  imports Main
begin

definition Swap_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Swap_precond X Y \<longleftrightarrow> True"

definition Swap :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "Swap X Y =
    (let x0 = X;
         y0 = Y;
         tmp = x0;
         x1 = y0;
         y1 = tmp
     in (x1, y1))"

definition Swap_postcond ::
    "int \<Rightarrow> int \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "Swap_postcond X Y result \<longleftrightarrow>
    fst result = Y \<and>
    snd result = X \<and>
    (X \<noteq> Y \<longrightarrow>
      fst result \<noteq> X \<and> snd result \<noteq> Y)"

theorem Swap_spec_satisfied:
  fixes X Y :: int
  assumes "Swap_precond X Y"
  shows "Swap_postcond X Y (Swap X Y)"
  sorry

end
