theory bignum_BigNum_add_cinqtvc
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
theorem add_cin'vc:
  fixes n1 :: "int list"
  fixes n2 :: "int list"
  fixes cin :: "int"
  assumes fact0: "valid n1"
  assumes fact1: "valid n2"
  assumes fact2: "(0 :: int) \<le> cin"
  assumes fact3: "cin \<le> (1 :: int)"
  shows "case n2 of Nil \<Rightarrow> (case n1 of Nil \<Rightarrow> valid n2 \<and> (0 :: int) \<le> cin \<and> cin < base | Cons x x1 \<Rightarrow> valid n1 \<and> (0 :: int) \<le> cin \<and> cin < base) | Cons x x1 \<Rightarrow> (case n1 of Nil \<Rightarrow> valid n2 \<and> (0 :: int) \<le> cin \<and> cin < base | Cons x2 x3 \<Rightarrow> (if cin + x2 + x < base then (case n1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x3) \<and> valid x3 \<and> valid x1 \<and> (0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> (1 :: int) else (case n1 of Nil \<Rightarrow> False | Cons _ f \<Rightarrow> f = x3) \<and> valid x3 \<and> valid x1 \<and> (0 :: int) \<le> (1 :: int) \<and> (1 :: int) \<le> (1 :: int)))"
  and "\<forall>(result :: int list). (case n2 of Nil \<Rightarrow> (case n1 of Nil \<Rightarrow> valid result \<and> value result = value n2 + cin | Cons x x1 \<Rightarrow> valid result \<and> value result = value n1 + cin) | Cons x x1 \<Rightarrow> (case n1 of Nil \<Rightarrow> valid result \<and> value result = value n2 + cin | Cons x2 x3 \<Rightarrow> (let d :: int = cin + x2 + x in if d < base then \<exists>(o1 :: int list). (valid o1 \<and> value o1 = value x3 + value x1 + (0 :: int)) \<and> result = Cons d o1 else \<exists>(o1 :: int list). (valid o1 \<and> value o1 = value x3 + value x1 + (1 :: int)) \<and> result = Cons (d - base) o1))) \<longrightarrow> valid result \<and> value result = value n1 + value n2 + cin"
  sorry
end
