theory rightmostbittrick_Rmbt_rightmost_bit_trickqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref"
begin
theorem rightmost_bit_trick'vc:
  fixes x :: "64 word"
  assumes fact0: "\<not>x = (0 :: 64 word)"
  shows "\<not>x = (0 :: 64 word)"
  and "\<forall>(p_bv :: 64 word). p_bv < (64 :: 64 word) \<and> bv_eq_sub_bv x (0 :: 64 word) (0 :: 64 word) p_bv \<and> (take_bit (unat p_bv) x \<noteq> (0)) = True \<longrightarrow> (let r :: 64 word = x AND -x in ((0 :: int) \<le> uint p_bv \<and> uint p_bv < (64 :: int)) \<and> bv_eq_sub x (0 :: 64 word) (0 :: int) (uint p_bv) \<and> (take_bit (nat (uint p_bv)) x \<noteq> (0)) = True \<and> bv_eq_sub r (0 :: 64 word) (0 :: int) (uint p_bv) \<and> bv_eq_sub r (0 :: 64 word) (uint p_bv + (1 :: int)) ((63 :: int) - uint p_bv) \<and> (take_bit (nat (uint p_bv)) r \<noteq> (0)) = True)"
  sorry
end
