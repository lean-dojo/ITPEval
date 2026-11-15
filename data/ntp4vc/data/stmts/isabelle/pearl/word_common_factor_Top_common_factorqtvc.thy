theory word_common_factor_Top_common_factorqtvc
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  char
consts power :: "char list \<Rightarrow> int \<Rightarrow> char list"
axiomatization where power'def:   "if n = (0 :: int) then power w n = [] else power w n = w @ power w (n - (1 :: int))"
 if "(0 :: int) \<le> n"
  for n :: "int"
  and w :: "char list"
theorem common_factor'vc:
  fixes a :: "char list"
  fixes b :: "char list"
  assumes fact0: "a @ b = b @ a"
  shows "let o1 :: int = int (length a) in (\<not>o1 = (0 :: int) \<longrightarrow> \<not>int (length b) = (0 :: int) \<longrightarrow> (if length a \<le> length b then let o2 :: int = int (length a) in ((0 :: int) \<le> o2 \<and> o2 \<le> int (length b)) \<and> (let c :: char list = drop (nat o2) b in b = a @ c \<and> (b = a @ c \<longrightarrow> ((0 :: int) \<le> int (length b) \<and> length c < length b) \<and> a @ c = c @ a)) else ((0 :: int) \<le> int (length a) \<and> length b < length a \<or> length a = length b \<and> (0 :: int) \<le> int (length b) \<and> length a < length b) \<and> b @ a = a @ b)) \<and> (\<forall>(w :: char list) (ka :: int) (kb :: int). (if o1 = (0 :: int) then w = b \<and> ka = (0 :: int) \<and> kb = (1 :: int) else if int (length b) = (0 :: int) then w = a \<and> ka = (1 :: int) \<and> kb = (0 :: int) else if length a \<le> length b then let c :: char list = drop (length a) b in b = a @ c \<and> (\<exists>(kb1 :: int). (((0 :: int) \<le> ka \<and> a = power w ka) \<and> (0 :: int) \<le> kb1 \<and> c = power w kb1) \<and> kb = ka + kb1) else ((0 :: int) \<le> kb \<and> b = power w kb) \<and> (0 :: int) \<le> ka \<and> a = power w ka) \<longrightarrow> ((0 :: int) \<le> ka \<and> a = power w ka) \<and> (0 :: int) \<le> kb \<and> b = power w kb)"
  sorry
end
