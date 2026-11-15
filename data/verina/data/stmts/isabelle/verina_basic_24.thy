(*
  Statement-only formalization of VERINA corpus artifact verina_basic_24
  (verina__isabelle__verina_basic_24), catalog title
  "firstEvenOddDifference": an executable integer-array scan records the
  first even and first odd entries and returns their difference, together
  with its existence precondition, first-occurrence postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_24
  imports Main
begin

definition isEven :: "int \<Rightarrow> bool" where
  "isEven n \<longleftrightarrow> n mod 2 = 0"

definition isOdd :: "int \<Rightarrow> bool" where
  "isOdd n \<longleftrightarrow> n mod 2 \<noteq> 0"

definition firstEvenOddDifference_precond :: "int list \<Rightarrow> bool" where
  "firstEvenOddDifference_precond a \<longleftrightarrow>
    length a > 1 \<and>
    (\<exists>x\<in>set a. isEven x) \<and>
    (\<exists>x\<in>set a. isOdd x)"

definition firstEvenOddDifference_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "firstEvenOddDifference_getBang a i =
    (if i < length a then a ! i else 0)"

fun firstEvenOddDifference_loop ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      nat option \<Rightarrow> nat option \<Rightarrow> int" where
  "firstEvenOddDifference_loop 0 a i firstEven firstOdd = 0"
| "firstEvenOddDifference_loop (Suc fuel) a i firstEven firstOdd =
    (if i < length a then
       (let x = firstEvenOddDifference_getBang a i;
            newEven =
              (if firstEven = None \<and> isEven x
               then Some i
               else firstEven);
            newOdd =
              (if firstOdd = None \<and> isOdd x
               then Some i
               else firstOdd)
        in if newEven \<noteq> None \<and> newOdd \<noteq> None
           then
             firstEvenOddDifference_getBang a (the newEven) -
               firstEvenOddDifference_getBang a (the newOdd)
           else
             firstEvenOddDifference_loop fuel a (i + 1) newEven newOdd)
     else 0)"

definition firstEvenOddDifference :: "int list \<Rightarrow> int" where
  "firstEvenOddDifference a =
    firstEvenOddDifference_loop (length a) a 0 None None"

definition firstEvenOddDifference_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "firstEvenOddDifference_postcond a result \<longleftrightarrow>
    (\<exists>i j.
      i < length a \<and>
      j < length a \<and>
      isEven (firstEvenOddDifference_getBang a i) \<and>
      isOdd (firstEvenOddDifference_getBang a j) \<and>
      result =
        firstEvenOddDifference_getBang a i -
          firstEvenOddDifference_getBang a j \<and>
      (\<forall>k. k < i \<longrightarrow>
        isOdd (firstEvenOddDifference_getBang a k)) \<and>
      (\<forall>k. k < j \<longrightarrow>
        isEven (firstEvenOddDifference_getBang a k)))"

theorem firstEvenOddDifference_spec_satisfied:
  assumes "firstEvenOddDifference_precond a"
  shows
    "firstEvenOddDifference_postcond a (firstEvenOddDifference a)"
  sorry

end
