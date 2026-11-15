theory ropes_Rope_subqtvc
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
theorem sub'vc:
  fixes r :: "rope"
  fixes len :: "int"
  fixes ofs :: "int"
  assumes fact0: "inv r"
  assumes fact1: "(0 :: int) \<le> len"
  assumes fact2: "(0 :: int) \<le> ofs"
  assumes fact3: "ofs \<le> length r"
  assumes fact4: "ofs + len \<le> length r"
  shows "case r of Emp \<Rightarrow> True | Str s ofs' _ \<Rightarrow> True | App r1 r2 _ \<Rightarrow> (let left1 :: int = length r1 - ofs; right1 :: int = len - left1 in if right1 \<le> (0 :: int) then (case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = r1 \<or> f1 = r1) \<and> inv r1 \<and> (0 :: int) \<le> len \<and> ((0 :: int) \<le> ofs \<and> ofs \<le> length r1) \<and> ofs + len \<le> length r1 else if left1 \<le> (0 :: int) then let o1 :: int = -left1 in (case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = r2 \<or> f1 = r2) \<and> inv r2 \<and> (0 :: int) \<le> len \<and> ((0 :: int) \<le> o1 \<and> o1 \<le> length r2) \<and> o1 + len \<le> length r2 else ((case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = r2 \<or> f1 = r2) \<and> inv r2 \<and> (0 :: int) \<le> right1 \<and> ((0 :: int) \<le> (0 :: int) \<and> (0 :: int) \<le> length r2) \<and> (0 :: int) + right1 \<le> length r2) \<and> (\<forall>(o1 :: rope). inv o1 \<and> infix_eqeq (string o1) (sub (string r2) (0 :: int) right1) \<longrightarrow> ((case r of Emp \<Rightarrow> False | Str _ _ _ \<Rightarrow> False | App f f1 _ \<Rightarrow> f = r1 \<or> f1 = r1) \<and> inv r1 \<and> (0 :: int) \<le> left1 \<and> ((0 :: int) \<le> ofs \<and> ofs \<le> length r1) \<and> ofs + left1 \<le> length r1) \<and> (\<forall>(o2 :: rope). inv o2 \<and> infix_eqeq (string o2) (sub (string r1) ofs left1) \<longrightarrow> inv o2 \<and> inv o1)))"
  and "\<forall>(result :: rope). (case r of Emp \<Rightarrow> result = Emp | Str s ofs' _ \<Rightarrow> (if len = (0 :: int) then result = Emp else result = Str s (ofs' + ofs) len) | App r1 r2 _ \<Rightarrow> (let left1 :: int = length r1 - ofs; right1 :: int = len - left1 in if right1 \<le> (0 :: int) then inv result \<and> infix_eqeq (string result) (sub (string r1) ofs len) else if left1 \<le> (0 :: int) then inv result \<and> infix_eqeq (string result) (sub (string r2) (-left1) len) else \<exists>(o1 :: rope). (inv o1 \<and> infix_eqeq (string o1) (sub (string r2) (0 :: int) right1)) \<and> (\<exists>(o2 :: rope). (inv o2 \<and> infix_eqeq (string o2) (sub (string r1) ofs left1)) \<and> inv result \<and> infix_eqeq (string result) (app (string o2) (string o1))))) \<longrightarrow> inv result \<and> infix_eqeq (string result) (sub (string r) ofs len)"
  sorry
end
