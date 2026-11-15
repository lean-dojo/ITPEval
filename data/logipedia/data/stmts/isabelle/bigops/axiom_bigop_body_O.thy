(*
  Statement-only formalization of Logipedia corpus artifact bigops.axiom_bigop_body_O:
  at index zero, the abstract big-operation body returns its supplied base value,
  uniformly over the result type. This file contains no proof.
*)

theory axiom_bigop_body_O
  imports Main
begin

consts
  bigop_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"

theorem axiom_bigop_body_O:
  "(bigop_body 0 ::
      (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a)
    = (\<lambda>p nil op f. nil)"
  sorry

end
