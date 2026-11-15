theory bignum_BigNum_add_digitqtvc
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
theorem add_digit'vc:
  fixes n :: "int list"
  fixes d :: "int"
  assumes fact0: "valid n"
  assumes fact1: "(0 :: int) \<le> d"
  assumes fact2: "d < base"
  shows "case n of Nil \<Rightarrow> True | Cons d0 r \<Rightarrow> \<not>d + d0 < base \<longrightarrow> (case n of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = r) \<and> valid r \<and> (0 :: int) \<le> (1 :: int) \<and> (1 :: int) < base"
  and "\<forall>(result :: int list). (case n of Nil \<Rightarrow> (if d = (0 :: int) then result = (Nil :: int list) else result = Cons d (Nil :: int list)) | Cons d0 r \<Rightarrow> (if d + d0 < base then result = Cons (d + d0) r else \<exists>(o1 :: int list). (valid o1 \<and> value o1 = value r + (1 :: int)) \<and> result = Cons (d + d0 - base) o1)) \<longrightarrow> valid result \<and> value result = value n + d"
  sorry
end
