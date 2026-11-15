(*
  Statement-only formalization of VERINA corpus artifact verina_basic_92
  (verina__isabelle__verina_basic_92), catalog title "SwapArithmetic": a
  total executable integer program swaps two values through subtraction and
  addition, together with its unconditional precondition, component-wise
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_92
  imports Main
begin

definition SwapArithmetic_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "SwapArithmetic_precond X Y \<longleftrightarrow> True"

definition SwapArithmetic :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "SwapArithmetic X Y =
    (let x1 = X;
         y1 = Y;
         x2 = y1 - x1;
         y2 = y1 - x2;
         x3 = y2 + x2
     in (x3, y2))"

definition SwapArithmetic_postcond ::
    "int \<Rightarrow> int \<Rightarrow> (int \<times> int) \<Rightarrow> bool" where
  "SwapArithmetic_postcond X Y result \<longleftrightarrow>
    fst result = Y \<and>
    snd result = X \<and>
    (X \<noteq> Y \<longrightarrow>
      fst result \<noteq> X \<and> snd result \<noteq> Y)"

theorem SwapArithmetic_spec_satisfied:
  fixes X Y :: int
  assumes "SwapArithmetic_precond X Y"
  shows "SwapArithmetic_postcond X Y (SwapArithmetic X Y)"
  sorry

end
