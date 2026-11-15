theory bitwalker_Bitwalker_poke_8bitqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = (take_bit (nat ((7 :: int) - pos emod (8 :: int))) (stream ! nat (pos ediv (8 :: int))) \<noteq> (0))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem poke_8bit'vc:
  fixes left1 :: "32 word"
  fixes flag :: "bool"
  fixes byte :: "8 word"
  assumes fact0: "uint left1 < (8 :: int)"
  shows "let o1 :: 8 word = u32_to_u8 left1 in (uint o1 \<le> (7 :: int) \<or> (7 :: 8 word) \<ge> o1) \<and> (let o2 :: 8 word = (7 :: 8 word) - o1 in uint o2 = (7 :: int) - uint o1 \<longrightarrow> (let mask :: 8 word = (1 :: 8 word) << unat o2 in (case flag of True \<Rightarrow> True | False \<Rightarrow> True) \<and> (\<forall>(result :: 8 word). (case flag of True \<Rightarrow> result = byte OR mask | False \<Rightarrow> result = byte AND not mask) \<longrightarrow> (\<forall>(i :: 32 word). i < (8 :: 32 word) \<longrightarrow> \<not>i = (7 :: 32 word) - left1 \<longrightarrow> (take_bit (unat (u32_to_u8 i)) result \<noteq> (0)) = (take_bit (unat (u32_to_u8 i)) byte \<noteq> (0))) \<and> (take_bit (unat ((7 :: 8 word) - u32_to_u8 left1)) result \<noteq> (0)) = flag)))"
  and "\<forall>(result :: 8 word). (\<forall>(i :: 32 word). i < (8 :: 32 word) \<longrightarrow> \<not>i = (7 :: 32 word) - left1 \<longrightarrow> (take_bit (unat (u32_to_u8 i)) result \<noteq> (0)) = (take_bit (unat (u32_to_u8 i)) byte \<noteq> (0))) \<and> (take_bit (unat ((7 :: 8 word) - u32_to_u8 left1)) result \<noteq> (0)) = flag \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (8 :: int) \<longrightarrow> \<not>i = (7 :: int) - uint left1 \<longrightarrow> (take_bit (nat i) result \<noteq> (0)) = (take_bit (nat i) byte \<noteq> (0))) \<and> (take_bit (nat ((7 :: int) - uint left1)) result \<noteq> (0)) = flag"
  sorry
end
