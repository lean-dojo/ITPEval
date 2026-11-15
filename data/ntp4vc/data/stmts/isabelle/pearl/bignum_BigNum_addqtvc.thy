theory bignum_BigNum_addqtvc
  imports "NTP4Verif.NTP4Verif"
begin
consts base :: "int"
axiomatization where base'def:   "(1 :: int) < base"
typedecl  digit
typedecl  num
fun "value" :: "int list \<Rightarrow> int"
  where "value (Nil :: int list) = (0 :: int)"
      | "value (Cons d r) = d + base * value r" for d r
fun valid :: "int list \<Rightarrow> _"
  where "valid (Nil :: int list) = True"
      | "valid (Cons d (Nil :: int list)) = ((0 :: int) < d \<and> d < base)" for d
      | "valid (Cons d r) = (((0 :: int) \<le> d \<and> d < base) \<and> valid r)" for d r
theorem add'vc:
  fixes n1 :: "int list"
  fixes n2 :: "int list"
  assumes fact0: "valid n1"
  assumes fact1: "valid n2"
  shows "valid n1"
  and "valid n2"
  and "(0 :: int) \<le> (0 :: int)"
  and "(0 :: int) \<le> (1 :: int)"
  and "\<forall>(result :: int list). valid result \<and> value result = value n1 + value n2 + (0 :: int) \<longrightarrow> valid result \<and> value result = value n1 + value n2"
  sorry
end
