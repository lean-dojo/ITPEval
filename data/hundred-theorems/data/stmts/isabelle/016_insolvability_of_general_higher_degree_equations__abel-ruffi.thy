(*
  Statement-only formalization of "Insolvability of General Higher Degree Equations
  (Abel-Ruffini)" from Hundred Theorems item 016. This file contains no proof.
*)

theory Abel_Ruffini
  imports Complex_Main
begin

datatype radical_expression =
    Rad_Const rat
  | Rad_Neg radical_expression
  | Rad_Inv radical_expression
  | Rad_Add radical_expression radical_expression
  | Rad_Mul radical_expression radical_expression
  | Rad_Pow radical_expression nat
  | Rad_Root nat radical_expression

inductive radical_value :: "radical_expression \<Rightarrow> complex \<Rightarrow> bool" where
  rational: "radical_value (Rad_Const q) (of_rat q)"
| negation: "radical_value e z \<Longrightarrow> radical_value (Rad_Neg e) (-z)"
| inverse: "radical_value e z \<Longrightarrow> radical_value (Rad_Inv e) (inverse z)"
| addition:
    "\<lbrakk>radical_value e1 z1; radical_value e2 z2\<rbrakk> \<Longrightarrow>
      radical_value (Rad_Add e1 e2) (z1 + z2)"
| multiplication:
    "\<lbrakk>radical_value e1 z1; radical_value e2 z2\<rbrakk> \<Longrightarrow>
      radical_value (Rad_Mul e1 e2) (z1 * z2)"
| power: "radical_value e z \<Longrightarrow> radical_value (Rad_Pow e n) (z ^ n)"
| root:
    "\<lbrakk>radical_value e z; n > 0; w ^ n = z\<rbrakk> \<Longrightarrow>
      radical_value (Rad_Root n e) w"

definition solvable_by_radicals :: "complex \<Rightarrow> bool" where
  "solvable_by_radicals z \<longleftrightarrow> (\<exists>e. radical_value e z)"

fun eval_rat_polynomial :: "rat list \<Rightarrow> complex \<Rightarrow> complex" where
  "eval_rat_polynomial [] z = 0"
| "eval_rat_polynomial (q # qs) z =
    of_rat q + z * eval_rat_polynomial qs z"

definition algebraic_over_rationals :: "complex \<Rightarrow> bool" where
  "algebraic_over_rationals z \<longleftrightarrow>
    (\<exists>qs :: rat list.
      (\<exists>q \<in> set qs. q \<noteq> 0) \<and> eval_rat_polynomial qs z = 0)"

theorem quintic_roots_not_solvable_by_radicals:
  fixes z :: complex
  assumes "z ^ 5 - 4 * z + 2 = 0"
  shows "\<not> solvable_by_radicals z"
  sorry

theorem abel_ruffini:
  "\<exists>z :: complex.
    algebraic_over_rationals z \<and> \<not> solvable_by_radicals z"
  sorry

end
