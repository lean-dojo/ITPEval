(*
  Statement-only formalization of VERINA corpus artifact verina_basic_99
  (verina__isabelle__verina_basic_99), catalog title "Triple": an executable
  integer program computes three times its input using distinct branches at
  the threshold 18, together with its unconditional precondition,
  integer-division postcondition, and final correctness proposition. This
  file contains no proof.
*)

theory verina_basic_99
  imports Main
begin

definition Triple_precond :: "int \<Rightarrow> bool" where
  "Triple_precond x \<longleftrightarrow> True"

definition Triple :: "int \<Rightarrow> int" where
  "Triple x =
    (if x < 18 then
       (let a = 2 * x;
            b = 4 * x
        in (a + b) div 2)
     else
       (let y = 2 * x
        in x + y))"

definition Triple_postcond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Triple_postcond x result \<longleftrightarrow>
    result div 3 = x \<and> result div 3 * 3 = result"

theorem Triple_spec_satisfied:
  assumes "Triple_precond x"
  shows "Triple_postcond x (Triple x)"
  sorry

end
