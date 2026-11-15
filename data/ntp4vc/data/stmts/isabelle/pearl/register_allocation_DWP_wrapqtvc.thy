theory register_allocation_DWP_wrapqtvc
  imports "NTP4Verif.NTP4Verif" "./register_allocation_Spec"
begin
typedecl  post
datatype  hcode = hcode'mk (hcode1: "instr list") (post1: "state \<Rightarrow> state \<Rightarrow> bool")
definition hcode_ok :: "hcode \<Rightarrow> _"
  where "hcode_ok hc \<longleftrightarrow> (\<forall>(s :: state). post1 hc s (exec_list (hcode1 hc) s) = True)" for hc
typedecl  trans
datatype  wcode = wcode'mk (trans1: "(state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool") (wcode1: "instr list")
definition wcode_ok :: "wcode \<Rightarrow> _"
  where "wcode_ok wc \<longleftrightarrow> (\<forall>(q :: state \<Rightarrow> bool) (s :: state). trans1 wc q s = True \<longrightarrow> q (exec_list (wcode1 wc) s) = True)" for wc
consts to_wp :: "(state \<Rightarrow> state \<Rightarrow> bool) \<Rightarrow> (state \<Rightarrow> bool) \<Rightarrow> state \<Rightarrow> bool"
axiomatization where to_wp'def:   "to_wp pst q s1 = True \<longleftrightarrow> (\<forall>(s2 :: state). pst s1 s2 = True \<longrightarrow> q s2 = True)"
  for pst :: "state \<Rightarrow> state \<Rightarrow> bool"
  and q :: "state \<Rightarrow> bool"
  and s1 :: "state"
consts rcompose :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c"
axiomatization where rcompose'def:   "rcompose f g x = g (f x)"
  for f :: "'a \<Rightarrow> 'b"
  and g :: "'b \<Rightarrow> 'c"
  and x :: "'a"
consts exec_closure :: "instr \<Rightarrow> state \<Rightarrow> state"
axiomatization where exec_closure'def:   "exec_closure i s = exec i s"
  for i :: "instr"
  and s :: "state"
consts id1 :: "'a \<Rightarrow> 'a"
axiomatization where id'def:   "id1 x = x"
  for x :: "'a"
theorem wrap'vc:
  fixes wc :: "wcode"
  fixes pst :: "state \<Rightarrow> state \<Rightarrow> bool"
  assumes fact0: "wcode_ok wc"
  assumes fact1: "\<forall>(x :: state). trans1 wc (pst x) x = True"
  shows "hcode_ok (hcode'mk (wcode1 wc) pst)"
  sorry
end
