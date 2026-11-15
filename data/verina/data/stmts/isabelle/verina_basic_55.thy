(*
  Statement-only formalization of VERINA corpus artifact verina_basic_55
  (verina__isabelle__verina_basic_55), catalog title "Compare": an executable
  integer equality comparison returns true exactly when its two inputs are
  equal, together with its unconditional precondition, postcondition, and
  final correctness proposition. This file contains no proof.
*)

theory verina_basic_55
  imports Main
begin

definition Compare_precond :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Compare_precond a b \<longleftrightarrow> True"

definition Compare :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "Compare a b = (if a = b then True else False)"

definition Compare_postcond ::
    "int \<Rightarrow> int \<Rightarrow> bool \<Rightarrow> bool" where
  "Compare_postcond a b result \<longleftrightarrow>
    (a = b \<longrightarrow> result = True) \<and>
    (a \<noteq> b \<longrightarrow> result = False)"

theorem Compare_spec_satisfied:
  assumes "Compare_precond a b"
  shows "Compare_postcond a b (Compare a b)"
  sorry

end
