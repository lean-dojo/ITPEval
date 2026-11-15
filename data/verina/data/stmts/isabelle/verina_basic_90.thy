(*
  Statement-only formalization of VERINA corpus artifact verina_basic_90
  (verina__isabelle__verina_basic_90), catalog title "SlopeSearch": an
  executable fuel-bounded slope search scans a nonempty rectangular integer
  matrix sorted by rows and columns for a key, returning its indices or
  (-1, -1), together with its precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_90
  imports Main
begin

definition SlopeSearch_row_getBang ::
    "int list list \<Rightarrow> nat \<Rightarrow> int list" where
  "SlopeSearch_row_getBang a i =
    (if i < length a then a ! i else [])"

definition SlopeSearch_int_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "SlopeSearch_int_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition get2d ::
    "int list list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "get2d a i j =
    SlopeSearch_int_getBang
      (SlopeSearch_row_getBang a (nat i))
      (nat j)"

fun SlopeSearch_pairwise ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "SlopeSearch_pairwise relation [] = True"
| "SlopeSearch_pairwise relation (x # xs) =
    (list_all (relation x) xs \<and>
     SlopeSearch_pairwise relation xs)"

definition SlopeSearch_precond ::
    "int list list \<Rightarrow> int \<Rightarrow> bool" where
  "SlopeSearch_precond a key \<longleftrightarrow>
    length a > 0 \<and>
    length (SlopeSearch_row_getBang a 0) > 0 \<and>
    SlopeSearch_pairwise
      (\<lambda>x y. length x = length y)
      a \<and>
    list_all
      (\<lambda>x. SlopeSearch_pairwise (\<lambda>u v. u \<le> v) x)
      a \<and>
    list_all
      (\<lambda>i.
        SlopeSearch_pairwise
          (\<lambda>u v. u \<le> v)
          (map (\<lambda>x. SlopeSearch_int_getBang x i) a))
      [0..<length (SlopeSearch_row_getBang a 0)]"

fun SlopeSearch_aux ::
    "int list list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<times> int" where
  "SlopeSearch_aux a key rows m n 0 = (-1, -1)"
| "SlopeSearch_aux a key rows m n (Suc fuel) =
    (if m \<ge> int rows \<or> n < 0 then
       (-1, -1)
     else if get2d a m n = key then
       (m, n)
     else if get2d a m n < key then
       SlopeSearch_aux a key rows (m + 1) n fuel
     else
       SlopeSearch_aux a key rows m (n - 1) fuel)"

definition SlopeSearch ::
    "int list list \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "SlopeSearch a key =
    (let rows = length a;
         cols =
           (if rows > 0
            then length (SlopeSearch_row_getBang a 0)
            else 0)
     in SlopeSearch_aux
          a key rows 0 (int (cols - 1)) (rows + cols))"

definition SlopeSearch_postcond ::
    "int list list \<Rightarrow> int \<Rightarrow> int \<times> int \<Rightarrow> bool" where
  "SlopeSearch_postcond a key result \<longleftrightarrow>
    (let m = fst result;
         n = snd result
     in
       (m \<ge> 0 \<and>
        m < int (length a) \<and>
        n \<ge> 0 \<and>
        n < int (length (SlopeSearch_row_getBang a 0)) \<and>
        get2d a m n = key) \<or>
       (m = -1 \<and>
        n = -1 \<and>
        list_all (\<lambda>x. list_all (\<lambda>e. e \<noteq> key) x) a))"

theorem SlopeSearch_spec_satisfied:
  fixes a :: "int list list" and key :: int
  assumes "SlopeSearch_precond a key"
  shows "SlopeSearch_postcond a key (SlopeSearch a key)"
  sorry

end
