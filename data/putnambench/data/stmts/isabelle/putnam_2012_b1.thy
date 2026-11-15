theory putnam_2012_b1 imports Complex_Main
begin

theorem putnam_2012_b1:
  fixes S :: "(real \<Rightarrow> real) set"
  (* Total representatives are identified by their values on the intended domain [0,\<infinity>). *)
  assumes Snonneg: "\<forall>f \<in> S. \<forall>x \<ge> 0. f x \<ge> 0"
    and Sext: "\<forall>f \<in> S. \<forall>g. (\<forall>x \<ge> 0. g x = f x) \<longrightarrow> g \<in> S"
    and f1: "(\<lambda>x. exp x - 1) \<in> S"
    and f2: "(\<lambda>x. ln (x + 1)) \<in> S"
    and hsum: "\<forall>f \<in> S. \<forall>g \<in> S. (\<lambda>x. f x + g x) \<in> S"
    and hcomp: "\<forall>f \<in> S. \<forall>g \<in> S. (\<lambda>x. f (g x)) \<in> S"
    and hdiff: "\<forall>f \<in> S. \<forall>g \<in> S.
      (\<forall>x \<ge> 0. f x \<ge> g x) \<longrightarrow> (\<lambda>x. f x - g x) \<in> S"
  shows "\<forall>f \<in> S. \<forall>g \<in> S. (\<lambda>x. f x * g x) \<in> S"
  sorry

end
