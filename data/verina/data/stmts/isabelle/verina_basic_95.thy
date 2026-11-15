(*
  Statement-only formalization of VERINA corpus artifact verina_basic_95
  (verina__isabelle__verina_basic_95), catalog title "swap": an executable
  integer-array program swaps the entries at two valid integer indices,
  together with its bounds precondition, complete array postcondition, and
  final correctness proposition. This file contains no proof.
*)

theory verina_basic_95
  imports Main
begin

definition swap_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "swap_getBang arr k =
    (if k < length arr then arr ! k else 0)"

definition swap_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "swap_setBang arr k x =
    (if k < length arr then list_update arr k x else arr)"

definition swap_precond ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "swap_precond arr i j \<longleftrightarrow>
    0 \<le> i \<and>
    0 \<le> j \<and>
    nat i < length arr \<and>
    nat j < length arr"

definition swap ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list" where
  "swap arr i j =
    (let i_nat = nat i;
         j_nat = nat j;
         arr1 = swap_setBang arr i_nat (swap_getBang arr j_nat);
         arr2 = swap_setBang arr1 j_nat (swap_getBang arr i_nat)
     in arr2)"

definition swap_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow>
      bool" where
  "swap_postcond arr i j result \<longleftrightarrow>
    length result = length arr \<and>
    swap_getBang result (nat i) = swap_getBang arr (nat j) \<and>
    swap_getBang result (nat j) = swap_getBang arr (nat i) \<and>
    (\<forall>k. k < length arr \<longrightarrow>
      k \<noteq> nat i \<longrightarrow>
      k \<noteq> nat j \<longrightarrow>
      swap_getBang result k = swap_getBang arr k)"

theorem swap_spec_satisfied:
  fixes arr :: "int list"
    and i j :: int
  assumes "swap_precond arr i j"
  shows "swap_postcond arr i j (swap arr i j)"
  sorry

end
