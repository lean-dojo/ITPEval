theory bitwalker_Bitwalker_poke_64bit_bvqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = (take_bit (nat ((7 :: int) - pos emod (8 :: int))) (stream ! nat (pos ediv (8 :: int))) \<noteq> (0))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem poke_64bit_bv'vc:
  fixes left1 :: "32 word"
  fixes flag :: "bool"
  fixes "value" :: "64 word"
  assumes fact0: "uint left1 < (64 :: int)"
  shows "uint left1 \<le> (63 :: int) \<or> (63 :: 32 word) \<ge> left1"
  and "let o1 :: 32 word = (63 :: 32 word) - left1 in uint o1 = (63 :: int) - uint left1 \<longrightarrow> (let mask :: 64 word = (1 :: 64 word) << unat (u32_to_u64 o1) in (case flag of True \<Rightarrow> True | False \<Rightarrow> True) \<and> (\<forall>(result :: 64 word). (case flag of True \<Rightarrow> result = value OR mask | False \<Rightarrow> result = value AND not mask) \<longrightarrow> (\<forall>(i :: 32 word). \<not>i = (63 :: 32 word) - left1 \<longrightarrow> (take_bit (unat (u32_to_u64 i)) result \<noteq> (0)) = (take_bit (unat (u32_to_u64 i)) value \<noteq> (0))) \<and> flag = (take_bit (unat (u32_to_u64 ((63 :: 32 word) - left1))) result \<noteq> (0))))"
  and "\<forall>(result :: 64 word). (\<forall>(i :: 32 word). \<not>i = (63 :: 32 word) - left1 \<longrightarrow> (take_bit (unat (u32_to_u64 i)) result \<noteq> (0)) = (take_bit (unat (u32_to_u64 i)) value \<noteq> (0))) \<and> flag = (take_bit (unat (u32_to_u64 ((63 :: 32 word) - left1))) result \<noteq> (0)) \<longrightarrow> (\<forall>(i :: int). ((0 :: int) \<le> i \<and> i < (64 :: int)) \<and> \<not>i = (63 :: int) - uint left1 \<longrightarrow> (take_bit (nat i) result \<noteq> (0)) = (take_bit (nat i) value \<noteq> (0))) \<and> flag = (take_bit (nat ((63 :: int) - uint left1)) result \<noteq> (0))"
  sorry
end
