(*
  Statement-only formalization of VERINA corpus artifact verina_basic_97
  (verina__isabelle__verina_basic_97), catalog title "TestArrayElements": an
  executable integer-array program sets the element at a valid natural-number
  index to 60, together with its bounds precondition, complete array
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_97
  imports Main
begin

definition TestArrayElements_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "TestArrayElements_getBang a k =
    (if k < length a then a ! k else 0)"

definition TestArrayElements_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "TestArrayElements_setBang a k x =
    (if k < length a then list_update a k x else a)"

definition TestArrayElements_precond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "TestArrayElements_precond a j \<longleftrightarrow>
    j < length a"

definition TestArrayElements ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "TestArrayElements a j =
    TestArrayElements_setBang a j 60"

definition TestArrayElements_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> bool" where
  "TestArrayElements_postcond a j result \<longleftrightarrow>
    length result = length a \<and>
    TestArrayElements_getBang result j = 60 \<and>
    (\<forall>k. k < length a \<longrightarrow>
      k \<noteq> j \<longrightarrow>
      TestArrayElements_getBang result k =
        TestArrayElements_getBang a k)"

theorem TestArrayElements_spec_satisfied:
  fixes a :: "int list"
    and j :: nat
  assumes "TestArrayElements_precond a j"
  shows
    "TestArrayElements_postcond a j (TestArrayElements a j)"
  sorry

end
