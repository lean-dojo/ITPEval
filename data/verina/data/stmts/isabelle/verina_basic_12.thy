(*
  Statement-only formalization of VERINA corpus artifact verina_basic_12,
  catalog title "cubeSurfaceArea": an executable natural-number program
  computes six times the square of a cube's edge length, together with its
  trivial precondition, surface-area postcondition, and correctness contract.
  This file contains no proof.
*)

theory verina_basic_12
  imports Main
begin

definition cubeSurfaceArea_precond :: "nat \<Rightarrow> bool" where
  "cubeSurfaceArea_precond edge \<longleftrightarrow> True"

definition cubeSurfaceArea :: "nat \<Rightarrow> nat" where
  "cubeSurfaceArea edge = 6 * edge * edge"

definition cubeSurfaceArea_postcond :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "cubeSurfaceArea_postcond edge result \<longleftrightarrow>
    result - 6 * edge * edge = 0 \<and>
    6 * edge * edge - result = 0"

theorem cubeSurfaceArea_spec_satisfied:
  assumes "cubeSurfaceArea_precond edge"
  shows "cubeSurfaceArea_postcond edge (cubeSurfaceArea edge)"
  sorry

end
