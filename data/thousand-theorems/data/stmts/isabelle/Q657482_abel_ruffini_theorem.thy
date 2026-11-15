(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q657482 (thousand-theorems__isabelle__Q657482), "Abel-Ruffini theorem":
  there exists a complex number algebraic over the rationals that is not
  solvable by radicals over the rationals. This file contains no proof.
*)

theory Q657482_abel_ruffini_theorem
  imports Complex_Main
begin

inductive q657482_solvable_by_radicals :: "complex \<Rightarrow> bool" where
  rational: "q657482_solvable_by_radicals (of_rat q)"
| negation:
    "q657482_solvable_by_radicals z \<Longrightarrow>
      q657482_solvable_by_radicals (-z)"
| inverse:
    "q657482_solvable_by_radicals z \<Longrightarrow>
      q657482_solvable_by_radicals (inverse z)"
| addition:
    "\<lbrakk>q657482_solvable_by_radicals z1;
      q657482_solvable_by_radicals z2\<rbrakk>
      \<Longrightarrow> q657482_solvable_by_radicals (z1 + z2)"
| multiplication:
    "\<lbrakk>q657482_solvable_by_radicals z1;
      q657482_solvable_by_radicals z2\<rbrakk>
      \<Longrightarrow> q657482_solvable_by_radicals (z1 * z2)"
| radical:
    "\<lbrakk>q657482_solvable_by_radicals (z ^ n); n > 0\<rbrakk>
      \<Longrightarrow> q657482_solvable_by_radicals z"

fun q657482_eval_rat_polynomial :: "rat list \<Rightarrow> complex \<Rightarrow> complex" where
  "q657482_eval_rat_polynomial [] z = 0"
| "q657482_eval_rat_polynomial (q # qs) z =
    of_rat q + z * q657482_eval_rat_polynomial qs z"

definition q657482_algebraic_over_rationals :: "complex \<Rightarrow> bool" where
  "q657482_algebraic_over_rationals z \<longleftrightarrow>
    (\<exists>qs :: rat list.
      (\<exists>q \<in> set qs. q \<noteq> 0) \<and>
      q657482_eval_rat_polynomial qs z = 0)"

theorem q657482_abel_ruffini:
  "\<exists>z :: complex.
    q657482_algebraic_over_rationals z \<and>
    \<not> q657482_solvable_by_radicals z"
  sorry

end
