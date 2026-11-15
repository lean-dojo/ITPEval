(*
  Statement-only formalization of Logipedia corpus artifact bigops.eq_bigop_body_O:
  Leibniz equality at index zero between the abstract big-operation body and
  the function returning its supplied base value, uniformly over the result
  type. This file contains no proof.
*)

theory eq_bigop_body_O
  imports Main
begin

consts
  bigop_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"

theorem eq_bigop_body_O:
  "(bigop_body 0 ::
      (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a)
    = (\<lambda>p nil op f. nil)"
  sorry

end
