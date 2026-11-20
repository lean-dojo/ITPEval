theory Sample
  imports Base
begin

locale bounded =
  fixes n :: nat
  assumes positive: "0 < n"
begin

lemma twice_positive: "0 < twice n"
  using positive by (simp add: twice_def)

end
end
