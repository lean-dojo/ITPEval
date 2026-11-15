(*
  Statement-only formalization of the thousand-theorems corpus artifact
  thousand-theorems__isabelle__Q192760, "Fundamental theorem of algebra":
  the complex numbers are algebraically closed, expressed by the defining
  coefficient-family root property for algebraically closed fields. This file
  contains no proof.
*)

theory Q192760_fundamental_theorem_of_algebra
  imports Complex_Main
begin

theorem q192760_fundamental_theorem_of_algebra:
  fixes f :: "nat \<Rightarrow> complex"
    and n :: nat
  assumes "n > 0"
    and "f n \<noteq> 0"
  shows "\<exists>z :: complex. (\<Sum>k\<le>n. f k * z ^ k) = 0"
  sorry

end
