(*
  Statement-only formalization of Logipedia corpus artifact
  bigops.sym_eq_bigop_body_O: Leibniz equality from the function returning its
  supplied base value to the abstract big-operation body at index zero,
  uniformly over the result type. This file contains no proof.
*)

theory sym_eq_bigop_body_O
  imports Main
begin

consts
  bigop_body ::
    "nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a"

theorem sym_eq_bigop_body_O:
  "(\<lambda>p nil op f. nil) =
    (bigop_body 0 ::
      (nat \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a)"
  sorry

end
