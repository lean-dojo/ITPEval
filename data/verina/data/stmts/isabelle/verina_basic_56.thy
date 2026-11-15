(*
  Statement-only formalization of VERINA corpus artifact verina_basic_56
  (verina__isabelle__verina_basic_56), catalog title "copy": an executable
  bounded segment-copy program replaces a destination segment by the
  corresponding source segment while preserving all other destination
  entries, together with its bounds precondition, postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_56
  imports Main
begin

definition copy_precond ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> bool" where
  "copy_precond src sStart dest dStart len \<longleftrightarrow>
    length src \<ge> sStart + len \<and>
    length dest \<ge> dStart + len"

definition copy_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "copy_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition copy_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "copy_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

fun updateSegment ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> int list" where
  "updateSegment r src sStart dStart 0 = r"
| "updateSegment r src sStart dStart (Suc n) =
    updateSegment
      (copy_setBang r (dStart + n) (copy_getBang src (sStart + n)))
      src sStart dStart n"

definition copy ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> int list" where
  "copy src sStart dest dStart len =
    (if len = 0
     then dest
     else
       (let r = dest
        in updateSegment r src sStart dStart len))"

definition copy_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> int list \<Rightarrow> bool" where
  "copy_postcond src sStart dest dStart len result \<longleftrightarrow>
    length result = length dest \<and>
    (\<forall>i. i < dStart \<longrightarrow>
      copy_getBang result i = copy_getBang dest i) \<and>
    (\<forall>i. dStart + len \<le> i \<longrightarrow> i < length result \<longrightarrow>
      copy_getBang result i = copy_getBang dest i) \<and>
    (\<forall>i. i < len \<longrightarrow>
      copy_getBang result (dStart + i) =
        copy_getBang src (sStart + i))"

theorem copy_spec_satisfied:
  assumes "copy_precond src sStart dest dStart len"
  shows
    "copy_postcond
      src sStart dest dStart len (copy src sStart dest dStart len)"
  sorry

end
