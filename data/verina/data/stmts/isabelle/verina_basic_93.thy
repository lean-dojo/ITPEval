(*
  Statement-only formalization of VERINA corpus artifact verina_basic_93
  (verina__isabelle__verina_basic_93), catalog title "SwapBitvectors": an
  executable XOR-based swap of two 8-bit unsigned words, together with its
  unconditional precondition, component-wise postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_93
  imports Main
begin

datatype uint8 =
  UInt8 bool bool bool bool bool bool bool bool

fun uint8_xor :: "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8" where
  "uint8_xor
      (UInt8 x7 x6 x5 x4 x3 x2 x1 x0)
      (UInt8 y7 y6 y5 y4 y3 y2 y1 y0) =
    UInt8
      (x7 \<noteq> y7) (x6 \<noteq> y6) (x5 \<noteq> y5) (x4 \<noteq> y4)
      (x3 \<noteq> y3) (x2 \<noteq> y2) (x1 \<noteq> y1) (x0 \<noteq> y0)"

definition SwapBitvectors_precond ::
    "uint8 \<Rightarrow> uint8 \<Rightarrow> bool" where
  "SwapBitvectors_precond X Y \<longleftrightarrow> True"

definition SwapBitvectors ::
    "uint8 \<Rightarrow> uint8 \<Rightarrow> uint8 \<times> uint8" where
  "SwapBitvectors X Y =
    (let temp = uint8_xor X Y;
         newY = uint8_xor temp Y;
         newX = uint8_xor temp newY
     in (newX, newY))"

definition SwapBitvectors_postcond ::
    "uint8 \<Rightarrow> uint8 \<Rightarrow> (uint8 \<times> uint8) \<Rightarrow> bool" where
  "SwapBitvectors_postcond X Y result \<longleftrightarrow>
    fst result = Y \<and>
    snd result = X \<and>
    (X \<noteq> Y \<longrightarrow>
      fst result \<noteq> X \<and> snd result \<noteq> Y)"

theorem SwapBitvectors_spec_satisfied:
  fixes X Y :: uint8
  assumes "SwapBitvectors_precond X Y"
  shows "SwapBitvectors_postcond X Y (SwapBitvectors X Y)"
  sorry

end
