theory queens_bv_Bits_rightmost_bit_trickqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "./queens_bv_S"
begin
typedecl  t
consts bv :: "t \<Rightarrow> 32 word"
consts mdl :: "t \<Rightarrow> int fset"
axiomatization where t'invariant:   "((0 :: int) \<le> i \<and> i < (32 :: int)) \<and> (take_bit (nat i) (bv self) \<noteq> (0)) = True \<longleftrightarrow> i |\<in>| mdl self"
  for i :: "int"
  and self :: "t"
definition t'eq :: "t \<Rightarrow> t \<Rightarrow> _"
  where "t'eq a b \<longleftrightarrow> bv a = bv b \<and> mdl a = mdl b" for a b
axiomatization where t'inj:   "a = b"
 if "t'eq a b"
  for a :: "t"
  and b :: "t"
theorem rightmost_bit_trick'vc:
  fixes a :: "t"
  assumes fact0: "\<not>mdl a = fempty"
  shows "let res :: 32 word = bv a AND -bv a; o1 :: int fset = finsert (Min (fset (mdl a))) fempty in (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (32 :: int)) \<and> (take_bit (nat i) res \<noteq> (0)) = True \<longleftrightarrow> i |\<in>| o1) \<and> (\<forall>(result :: t). bv result = res \<and> mdl result = o1 \<longrightarrow> mdl result = finsert (Min (fset (mdl a))) fempty)"
  sorry
end
