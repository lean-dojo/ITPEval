theory there_and_back_again_Convolution_convolutionqtvc
  imports "NTP4Verif.NTP4Verif"
begin
theorem convolution'vc:
  fixes x :: "'a list"
  fixes y :: "'a list"
  assumes fact0: "length x = length y"
  shows "length x \<le> length y"
  and "\<forall>(o1 :: ('a \<times> 'a) list) (o2 :: 'a list). (\<exists>(y0 :: 'a list). y = y0 @ o2 \<and> length y0 = length x \<and> o1 = zip x (rev y0)) \<longrightarrow> o1 = zip x (rev y)"
  sorry
end
