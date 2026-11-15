theory bitwalker_Bitwalker_pokethenpeekqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "mach.bv_BVCheck8" "mach.bv_BVCheck32" "mach.bv_BVCheck64"
begin
definition nth8_stream :: "8 word list \<Rightarrow> int \<Rightarrow> bool"
  where "nth8_stream stream pos = (take_bit (nat ((7 :: int) - pos emod (8 :: int))) (stream ! nat (pos ediv (8 :: int))) \<noteq> (0))" for stream pos
definition maxvalue :: "32 word \<Rightarrow> 64 word"
  where "maxvalue len = (1 :: 64 word) << unat (u32_to_u64 len)" for len
theorem pokethenpeek'vc:
  fixes addr :: "8 word list"
  fixes len :: "32 word"
  fixes start :: "32 word"
  fixes "value" :: "64 word"
  assumes fact0: "(8 :: int) * int (length addr) < (4294967296 :: int)"
  assumes fact1: "(0 :: int) \<le> uint len"
  assumes fact2: "uint len < (64 :: int)"
  assumes fact3: "uint start + uint len \<le> (8 :: int) * int (length addr)"
  assumes fact4: "uint value < uint (maxvalue len)"
  shows "uint len < (64 :: int)"
  and "uint start + uint len < (4294967296 :: int)"
  and "(8 :: int) * int (length addr) < (4294967296 :: int)"
  and "\<forall>(addr1 :: 8 word list). length addr1 = length addr \<longrightarrow> (\<forall>(poke_result :: int). (-(2 :: int) \<le> poke_result \<and> poke_result \<le> (0 :: int)) \<and> (poke_result = -(1 :: int) \<longleftrightarrow> (8 :: int) * int (length addr1) < uint start + uint len) \<and> (poke_result = -(2 :: int) \<longleftrightarrow> uint (maxvalue len) \<le> uint value \<and> uint start + uint len \<le> (8 :: int) * int (length addr1)) \<and> (poke_result = (0 :: int) \<longleftrightarrow> uint value < uint (maxvalue len) \<and> uint start + uint len \<le> (8 :: int) * int (length addr1)) \<and> (poke_result = (0 :: int) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < uint start \<longrightarrow> nth8_stream addr i = nth8_stream addr1 i) \<and> (\<forall>(i :: int). uint start \<le> i \<and> i < uint start + uint len \<longrightarrow> nth8_stream addr1 i = (take_bit (nat (uint len - i - (1 :: int) + uint start)) value \<noteq> (0))) \<and> (\<forall>(i :: int). uint start + uint len \<le> i \<and> i < (8 :: int) * int (length addr1) \<longrightarrow> nth8_stream addr1 i = nth8_stream addr i)) \<longrightarrow> (uint len \<le> (64 :: int) \<and> uint start + uint len < (4294967296 :: int) \<and> (8 :: int) * int (length addr1) < (4294967296 :: int)) \<and> (\<forall>(peek_result :: 64 word). ((8 :: int) * int (length addr1) < uint start + uint len \<longrightarrow> peek_result = (0 :: 64 word)) \<and> (uint start + uint len \<le> (8 :: int) * int (length addr1) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < uint len \<longrightarrow> (take_bit (nat i) peek_result \<noteq> (0)) = nth8_stream addr1 (uint start + uint len - i - (1 :: int))) \<and> (\<forall>(i :: int). uint len \<le> i \<and> i < (64 :: int) \<longrightarrow> (take_bit (nat i) peek_result \<noteq> (0)) = False)) \<longrightarrow> peek_result = value))"
  sorry
end
