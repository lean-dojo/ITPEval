theory queens_bv_Bits_belowqtvc
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
theorem below'vc:
  fixes n :: "32 word"
  assumes fact0: "n \<le> (32 :: 32 word)"
  shows "let o1 :: int fset = Ico_fset_int (0 :: int) (uint n); o2 :: 32 word = not ((4294967295 :: 32 word) << unat n) in (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (32 :: int)) \<and> (take_bit (nat i) o2 \<noteq> (0)) = True \<longleftrightarrow> i |\<in>| o1) \<and> (\<forall>(result :: t). bv result = o2 \<and> mdl result = o1 \<longrightarrow> mdl result = Ico_fset_int (0 :: int) (uint n))"
  sorry
end
