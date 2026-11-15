theory bitcount_AsciiCode_asciiqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.WellFounded_WellFounded" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "./bitcount_BitCounting32" "mach.bv_BVCheck32"
begin
definition validAscii :: "32 word \<Rightarrow> _"
  where "validAscii b \<longleftrightarrow> even (count_logic b)" for b
consts fun_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
axiomatization where fun_or'def:   "fun_or f g x = True \<longleftrightarrow> f x = True \<or> g x = True"
  for f :: "'a \<Rightarrow> bool"
  and g :: "'a \<Rightarrow> bool"
  and x :: "'a"
theorem ascii'vc:
  fixes b :: "32 word"
  fixes c :: "32 word"
  assumes fact0: "\<not>(take_bit (unat (w32_size_bv - (1 :: 32 word))) b \<noteq> (0)) = True"
  assumes fact1: "uint c = count_logic b"
  shows "(31 :: 32 word) < w32_size_bv \<or> (31 :: int) < (32 :: int)"
  and "let maskbit :: 32 word = c << unat (31 :: 32 word) in maskbit = c << (31 :: nat) \<longrightarrow> (let code :: 32 word = b OR maskbit in bv_eq_sub_bv code b (0 :: 32 word) (w32_size_bv - (1 :: 32 word)) \<and> validAscii code)"
  sorry
end
