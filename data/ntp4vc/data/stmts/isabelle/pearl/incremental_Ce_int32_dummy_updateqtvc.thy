theory incremental_Ce_int32_dummy_updateqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref"
begin
theorem dummy_update'vc:
  fixes r :: "32 word"
  assumes fact0: "sint r = (22 :: int)"
  shows "int'32_in_bounds (42 :: int)"
  and "\<forall>(o1 :: 32 word). sint o1 = (42 :: int) \<longrightarrow> int'32_in_bounds (sint o1 + sint o1) \<and> (\<forall>(o2 :: 32 word). sint o2 = sint o1 + sint o1 \<longrightarrow> sint o2 = (42 :: int))"
  sorry
end
