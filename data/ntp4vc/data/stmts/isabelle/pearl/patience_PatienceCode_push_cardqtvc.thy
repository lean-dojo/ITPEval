theory patience_PatienceCode_push_cardqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  card
fun wf_stacks :: "int list list \<Rightarrow> _"
  where "wf_stacks (Nil :: int list list) = True"
      | "wf_stacks (Cons (Nil :: int list) x) = False" for x
      | "wf_stacks (Cons (Cons x x0) rem) = wf_stacks rem" for x x0 rem
theorem push_card'vc:
  fixes stacks1 :: "int list list"
  fixes acc :: "int list list"
  fixes c :: "int"
  assumes fact0: "wf_stacks stacks1"
  assumes fact1: "wf_stacks acc"
  shows "case stacks1 of Nil \<Rightarrow> True | Cons stack remaining_stacks \<Rightarrow> (case stack of Nil \<Rightarrow> False | Cons c' _ \<Rightarrow> \<not>c \<le> c' \<longrightarrow> (case stacks1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = remaining_stacks) \<and> wf_stacks remaining_stacks \<and> wf_stacks (Cons stack acc))"
  and "\<forall>(result :: int list list). (case stacks1 of Nil \<Rightarrow> result = rev (Cons (Cons c (Nil :: int list)) acc) @ (Nil :: int list list) | Cons stack remaining_stacks \<Rightarrow> (case stack of Nil \<Rightarrow> False | Cons c' _ \<Rightarrow> (if c \<le> c' then result = rev (Cons (Cons c stack) acc) @ remaining_stacks else wf_stacks result))) \<longrightarrow> wf_stacks result"
  sorry
end
