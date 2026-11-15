(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_I_gen:
  reindexing a Boolean-filtered natural-number product from a shifted interval
  to the equivalent lower-bounded prefix. This file contains no proof.
*)

theory bigop_I_gen
  imports Main
begin

fun bigop ::
  "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
    ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "bigop 0 p nil op f = nil"
| "bigop (Suc n) p nil op f =
    (if p n
     then op (f n) (bigop n p nil op f)
     else bigop n p nil op f)"

theorem bigop_I_gen:
  fixes a b :: nat
    and p :: "nat \<Rightarrow> bool"
    and f :: "nat \<Rightarrow> nat"
  assumes "a \<le> b"
  shows
    "bigop (b - a) (\<lambda>i. p (i + a)) 1 (*) (\<lambda>i. f (i + a)) =
      bigop b (\<lambda>i. a \<le> i \<and> p i) 1 (*) f"
  sorry

end
