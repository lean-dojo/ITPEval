(*
  Statement-only formalization of Logipedia corpus artifact bigops.bigop_false:
  a Boolean-filtered polymorphic big operation with a constantly false
  predicate equals its supplied neutral value. This file contains no proof.
*)

theory bigop_false
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

theorem bigop_false:
  fixes n :: nat
    and nil :: 'a
    and op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and f :: "nat \<Rightarrow> 'a"
  shows "bigop n (\<lambda>i. False) nil op f = nil"
  sorry

end
