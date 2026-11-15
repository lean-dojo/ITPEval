theory ropes_Rope_getqtvc
  imports "NTP4Verif.NTP4Verif" "./ropes_MyString"
begin
datatype  rope = Emp | Str "char_string" "int" "int" | App "rope" "rope" "int"
definition length :: "rope \<Rightarrow> int"
  where "length r = (case r of Emp \<Rightarrow> (0 :: int) | Str _ _ len \<Rightarrow> len | App _ _ len \<Rightarrow> len)" for r
fun inv :: "rope \<Rightarrow> _"
  where "inv Emp = True"
      | "inv (Str s ofs len) = ((0 :: int) < len \<and> ((0 :: int) \<le> ofs \<and> ofs < ropes_MyString.length s) \<and> ofs + len \<le> ropes_MyString.length s)" for s ofs len
      | "inv (App l r1 len) = ((0 :: int) < length l \<and> inv l \<and> (0 :: int) < length r1 \<and> inv r1 \<and> len = length l + length r1)" for l r1 len
fun string :: "rope \<Rightarrow> char_string"
  where "string Emp = empty"
      | "string (Str s ofs len) = sub s ofs len" for s ofs len
      | "string (App l r1 x) = app (string l) (string r1)" for l r1 x
consts empty :: "rope"
axiomatization where empty'def'0:   "length empty = (0 :: int)"
axiomatization where empty'def'1:   "inv empty"
axiomatization where empty'def'2:   "infix_eqeq (string empty) ropes_MyString.empty"
theorem get'vc:
  fixes r :: "rope"
  fixes i :: "int"
  assumes fact0: "inv r"
  assumes fact1: "(0 :: int) \<le> i"
  assumes fact2: "i < length r"
  shows "case r of Emp \<Rightarrow> False | Str s ofs _ \<Rightarrow> (let o1 :: int = ofs + i in (0 :: int) \<le> o1 \<and> o1 < ropes_MyString.length s) | App left1 right1 _ \<Rightarrow> (let n :: int = length left1 in if i < n then (case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = left1 \<or> f1 = left1) \<and> inv left1 \<and> (0 :: int) \<le> i \<and> i < length left1 else let o1 :: int = i - n in (case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = right1 \<or> f1 = right1) \<and> inv right1 \<and> (0 :: int) \<le> o1 \<and> o1 < length right1)"
  and "\<forall>(result :: ropes_MyString.char). (case r of Emp \<Rightarrow> False | Str s ofs _ \<Rightarrow> result = mixfix_lbrb s (ofs + i) | App left1 right1 _ \<Rightarrow> (let n :: int = length left1 in if i < n then result = mixfix_lbrb (string left1) i else result = mixfix_lbrb (string right1) (i - n))) \<longrightarrow> result = mixfix_lbrb (string r) i"
  sorry
end
