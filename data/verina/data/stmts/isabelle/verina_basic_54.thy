(*
  Statement-only formalization of VERINA corpus artifact verina_basic_54
  (verina__isabelle__verina_basic_54), catalog title "CanyonSearch": an
  executable two-pointer search computes the minimum absolute difference
  between elements of two nonempty pairwise nondecreasing integer arrays,
  together with its precondition, postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_54
  imports Main
begin

definition canyonSearch_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "canyonSearch_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition canyonSearch_natAbs :: "int \<Rightarrow> nat" where
  "canyonSearch_natAbs x = nat (abs x)"

fun canyonSearch_pairwise_le :: "int list \<Rightarrow> bool" where
  "canyonSearch_pairwise_le [] = True"
| "canyonSearch_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     canyonSearch_pairwise_le xs)"

definition CanyonSearch_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "CanyonSearch_precond a b \<longleftrightarrow>
    length a > 0 \<and>
    length b > 0 \<and>
    canyonSearch_pairwise_le a \<and>
    canyonSearch_pairwise_le b"

fun canyonSearchAux_steps ::
    "nat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "canyonSearchAux_steps 0 a b m n d = d"
| "canyonSearchAux_steps (Suc fuel) a b m n d =
    (if m < length a \<and> n < length b then
       let diff =
         canyonSearch_natAbs
           (canyonSearch_getBang a m - canyonSearch_getBang b n);
           new_d = (if diff < d then diff else d)
       in if canyonSearch_getBang a m \<le> canyonSearch_getBang b n
          then canyonSearchAux_steps fuel a b (m + 1) n new_d
          else canyonSearchAux_steps fuel a b m (n + 1) new_d
     else d)"

definition canyonSearchAux ::
    "int list \<Rightarrow> int list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "canyonSearchAux a b m n d =
    canyonSearchAux_steps (length a + length b - m - n) a b m n d"

definition CanyonSearch :: "int list \<Rightarrow> int list \<Rightarrow> nat" where
  "CanyonSearch a b =
    (let a0 = canyonSearch_getBang a 0;
         b0 = canyonSearch_getBang b 0;
         init =
           (if a0 < b0
            then canyonSearch_natAbs (b0 - a0)
            else canyonSearch_natAbs (a0 - b0))
     in canyonSearchAux a b 0 0 init)"

definition CanyonSearch_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> bool" where
  "CanyonSearch_postcond a b result \<longleftrightarrow>
    (\<exists>ai\<in>set a. \<exists>bi\<in>set b.
      result = canyonSearch_natAbs (ai - bi)) \<and>
    (\<forall>ai\<in>set a. \<forall>bi\<in>set b.
      result \<le> canyonSearch_natAbs (ai - bi))"

theorem CanyonSearch_spec_satisfied:
  assumes "CanyonSearch_precond a b"
  shows "CanyonSearch_postcond a b (CanyonSearch a b)"
  sorry

end
