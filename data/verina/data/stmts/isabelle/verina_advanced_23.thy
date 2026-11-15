(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_23,
  catalog title "isPowerOfTwo": an executable fuel-bounded integer program
  decides whether its input is a positive power of two, together with its
  precondition and Boolean correctness contract. This file contains no proof.
*)

theory verina_advanced_23
  imports Main
begin

definition isPowerOfTwo_precond :: "int \<Rightarrow> bool" where
  "isPowerOfTwo_precond n \<longleftrightarrow> True"

fun isPowerOfTwo_aux :: "int \<Rightarrow> nat \<Rightarrow> bool" where
  "isPowerOfTwo_aux m 0 = False"
| "isPowerOfTwo_aux m (Suc fuel) =
    (if m = 1
     then True
     else if m mod 2 \<noteq> 0
     then False
     else isPowerOfTwo_aux (m div 2) fuel)"

definition isPowerOfTwo :: "int \<Rightarrow> bool" where
  "isPowerOfTwo n =
    (if n \<le> 0
     then False
     else isPowerOfTwo_aux n (nat (abs n)))"

fun isPowerOfTwo_pow :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "isPowerOfTwo_pow base 0 = 1"
| "isPowerOfTwo_pow base (Suc exp) =
    base * isPowerOfTwo_pow base exp"

definition isPowerOfTwo_postcond ::
    "int \<Rightarrow> bool \<Rightarrow> bool" where
  "isPowerOfTwo_postcond n result \<longleftrightarrow>
    (if result
     then \<exists>x::nat. isPowerOfTwo_pow 2 x = n \<and> n > 0
     else \<not> (\<exists>x::nat. isPowerOfTwo_pow 2 x = n \<and> n > 0))"

theorem isPowerOfTwo_spec_satisfied:
  assumes "isPowerOfTwo_precond n"
  shows "isPowerOfTwo_postcond n (isPowerOfTwo n)"
  sorry

end
