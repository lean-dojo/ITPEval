(*
  Statement-only formalization of VERINA corpus artifact verina_basic_23
  (verina__isabelle__verina_basic_23), catalog title "differenceMinMax":
  an executable nonempty integer-array scan initializes from the first value,
  tracks the running minimum and maximum, and returns their difference,
  together with its fold-based postcondition and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_23
  imports Main
begin

definition differenceMinMax_precond :: "int list \<Rightarrow> bool" where
  "differenceMinMax_precond a \<longleftrightarrow> length a > 0"

definition differenceMinMax_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "differenceMinMax_getBang a i =
    (if i < length a then a ! i else 0)"

fun differenceMinMax_loop ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "differenceMinMax_loop 0 a i minVal maxVal = maxVal - minVal"
| "differenceMinMax_loop (Suc fuel) a i minVal maxVal =
    (if i < length a then
       (let x = differenceMinMax_getBang a i;
            newMin = (if x < minVal then x else minVal);
            newMax = (if x > maxVal then x else maxVal)
        in differenceMinMax_loop fuel a (i + 1) newMin newMax)
     else maxVal - minVal)"

definition differenceMinMax :: "int list \<Rightarrow> int" where
  "differenceMinMax a =
    differenceMinMax_loop
      (length a) a 1
      (differenceMinMax_getBang a 0)
      (differenceMinMax_getBang a 0)"

definition differenceMinMax_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "differenceMinMax_postcond a result \<longleftrightarrow>
    result +
      foldl
        (\<lambda>acc x. if x < acc then x else acc)
        (differenceMinMax_getBang a 0) a =
    foldl
      (\<lambda>acc x. if x > acc then x else acc)
      (differenceMinMax_getBang a 0) a"

theorem differenceMinMax_spec_satisfied:
  assumes "differenceMinMax_precond a"
  shows "differenceMinMax_postcond a (differenceMinMax a)"
  sorry

end
