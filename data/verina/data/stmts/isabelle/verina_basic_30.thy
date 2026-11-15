(*
  Statement-only formalization of VERINA corpus artifact verina_basic_30
  (verina__isabelle__verina_basic_30), catalog title "elementWiseModulo": an
  executable integer-array program computes the Euclidean remainder of each
  entry of one nonempty array by the corresponding nonzero entry of an
  equal-length array, together with its precondition, pointwise postcondition,
  and final correctness proposition. This file contains no proof.
*)

theory verina_basic_30
  imports Main
begin

definition elementWiseModulo_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "elementWiseModulo_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition leanIntEmod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "leanIntEmod x y =
    (if y = 0 then x else x mod \<bar>y\<bar>)"

definition elementWiseModulo_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "elementWiseModulo_precond a b \<longleftrightarrow>
    length a = length b \<and>
    length a > 0 \<and>
    (\<forall>i<length b. elementWiseModulo_getBang b i \<noteq> 0)"

definition elementWiseModulo ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "elementWiseModulo a b =
    map
      (\<lambda>(i, x).
        leanIntEmod x (elementWiseModulo_getBang b i))
      (zip [0..<length a] a)"

definition elementWiseModulo_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "elementWiseModulo_postcond a b result \<longleftrightarrow>
    length result = length a \<and>
    (\<forall>i<length result.
      elementWiseModulo_getBang result i =
        leanIntEmod
          (elementWiseModulo_getBang a i)
          (elementWiseModulo_getBang b i))"

theorem elementWiseModulo_spec_satisfied:
  assumes "elementWiseModulo_precond a b"
  shows
    "elementWiseModulo_postcond a b (elementWiseModulo a b)"
  sorry

end
