(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_diff:
  factoring a selected term from a Boolean-filtered finite product over a
  natural-number prefix. This file contains no proof.
*)

theory bigop_diff
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

theorem bigop_diff:
  fixes p :: "nat \<Rightarrow> bool"
    and f :: "nat \<Rightarrow> nat"
    and i n :: nat
  assumes "i < n"
    and "p i = True"
  shows
    "bigop n p 1 (*) f =
      f i * bigop n (\<lambda>x. i \<noteq> x \<and> p x) 1 (*) f"
  oops

end
