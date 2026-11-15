theory there_and_back_again_Convolution_convolution_recqtvc
  imports "NTP4Verif.NTP4Verif"
begin
theorem convolution_rec'vc:
  fixes x :: "'a list"
  fixes y :: "'a list"
  assumes fact0: "length x \<le> length y"
  shows "case x of (Nil :: 'a list) \<Rightarrow> True | Cons x0 xs \<Rightarrow> ((case x of (Nil :: 'a list) \<Rightarrow> False | Cons _ f \<Rightarrow> f = xs) \<and> length xs \<le> length y) \<and> (\<forall>(o1 :: ('a \<times> 'a) list) (o2 :: 'a list). (\<exists>(y0 :: 'a list). y = y0 @ o2 \<and> length y0 = length xs \<and> o1 = zip xs (rev y0)) \<longrightarrow> (case o2 of Cons x1 x2 \<Rightarrow> True | _ \<Rightarrow> False))"
  and "\<forall>(r :: ('a \<times> 'a) list) (ys :: 'a list). (case x of (Nil :: 'a list) \<Rightarrow> r = (Nil :: ('a \<times> 'a) list) \<and> ys = y | Cons x0 xs \<Rightarrow> (\<exists>(r1 :: ('a \<times> 'a) list) (ys1 :: 'a list). (\<exists>(y0 :: 'a list). y = y0 @ ys1 \<and> length y0 = length xs \<and> r1 = zip xs (rev y0)) \<and> (case ys1 of Cons x1 x2 \<Rightarrow> r = Cons (x0, x1) r1 \<and> ys = x2 | _ \<Rightarrow> False))) \<longrightarrow> (\<exists>(y0 :: 'a list). y = y0 @ ys \<and> length y0 = length x \<and> r = zip x (rev y0))"
  sorry
end
