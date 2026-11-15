(*
  Statement-only formalization of the thousand-theorems corpus artifact Q791663
  (thousand-theorems__isabelle__Q791663), "Beatty's theorem": complementary
  floor and ceiling Beatty sets, and the partition of the positive integers by
  irrational conjugate Beatty sequences. This file contains no proof.
*)

theory Q791663_beatty_s_theorem
  imports Complex_Main
begin

definition q791663_holder_conjugate :: "real \<Rightarrow> real \<Rightarrow> bool" where
  "q791663_holder_conjugate r s \<longleftrightarrow>
    0 < r \<and> 0 < s \<and> inverse r + inverse s = 1"

definition q791663_beatty_seq :: "real \<Rightarrow> int \<Rightarrow> int" where
  "q791663_beatty_seq r k = floor (of_int k * r)"

definition q791663_beatty_seq' :: "real \<Rightarrow> int \<Rightarrow> int" where
  "q791663_beatty_seq' r k = ceiling (of_int k * r) - 1"

definition q791663_beatty_set :: "real \<Rightarrow> int set" where
  "q791663_beatty_set r = range (q791663_beatty_seq r)"

definition q791663_beatty_set' :: "real \<Rightarrow> int set" where
  "q791663_beatty_set' r = range (q791663_beatty_seq' r)"

definition q791663_positive_beatty_set :: "real \<Rightarrow> int set" where
  "q791663_positive_beatty_set r =
    q791663_beatty_seq r ` {k::int. 0 < k}"

definition q791663_symm_diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "q791663_symm_diff A B = (A - B) \<union> (B - A)"

theorem compl_beattySeq:
  fixes r s :: real
  assumes "q791663_holder_conjugate r s"
  shows "UNIV - q791663_beatty_set r = q791663_beatty_set' s"
  sorry

theorem irrational_beattySeq_symmDiff_beattySeq_pos:
  fixes r s :: real
  assumes "q791663_holder_conjugate r s"
    and "r \<notin> \<rat>"
  shows "q791663_symm_diff
      (q791663_positive_beatty_set r)
      (q791663_positive_beatty_set s) =
    {n::int. 0 < n}"
  sorry

end
