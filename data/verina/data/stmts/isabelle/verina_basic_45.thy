(*
  Statement-only formalization of VERINA corpus artifact verina_basic_45
  (verina__isabelle__verina_basic_45), catalog title "findProduct": an
  executable integer-list program locates the first even and first odd entries
  and returns their product, together with its existence precondition,
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_45
  imports Main
begin

definition isEven :: "int \<Rightarrow> bool" where
  "isEven n = (n mod 2 = 0)"

definition isOdd :: "int \<Rightarrow> bool" where
  "isOdd n = (n mod 2 \<noteq> 0)"

fun findProduct_findIdxFrom ::
    "(int \<Rightarrow> bool) \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      nat option" where
  "findProduct_findIdxFrom p [] i = None"
| "findProduct_findIdxFrom p (x # xs) i =
    (if p x
     then Some i
     else findProduct_findIdxFrom p xs (Suc i))"

definition findProduct_findIdx ::
    "(int \<Rightarrow> bool) \<Rightarrow> int list \<Rightarrow> nat option" where
  "findProduct_findIdx p xs = findProduct_findIdxFrom p xs 0"

definition firstEvenOddIndices ::
    "int list \<Rightarrow> (nat \<times> nat) option" where
  "firstEvenOddIndices xs =
    (let evenIndex = findProduct_findIdx isEven xs;
         oddIndex = findProduct_findIdx isOdd xs
     in case evenIndex of
          None \<Rightarrow> None
        | Some ei \<Rightarrow>
            (case oddIndex of
               None \<Rightarrow> None
             | Some oi \<Rightarrow> Some (ei, oi)))"

definition findProduct_precond :: "int list \<Rightarrow> bool" where
  "findProduct_precond xs \<longleftrightarrow>
    length xs > 1 \<and>
    (\<exists>x\<in>set xs. isEven x) \<and>
    (\<exists>x\<in>set xs. isOdd x)"

definition findProduct_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "findProduct_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition findProduct :: "int list \<Rightarrow> int" where
  "findProduct xs =
    (case firstEvenOddIndices xs of
       None \<Rightarrow> 0
     | Some (ei, oi) \<Rightarrow>
         findProduct_getBang xs ei * findProduct_getBang xs oi)"

definition findProduct_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "findProduct_postcond xs result \<longleftrightarrow>
    (case firstEvenOddIndices xs of
       None \<Rightarrow> True
     | Some (ei, oi) \<Rightarrow>
         result =
           findProduct_getBang xs ei * findProduct_getBang xs oi)"

theorem findProduct_spec_satisfied:
  assumes "findProduct_precond xs"
  shows "findProduct_postcond xs (findProduct xs)"
  sorry

end
