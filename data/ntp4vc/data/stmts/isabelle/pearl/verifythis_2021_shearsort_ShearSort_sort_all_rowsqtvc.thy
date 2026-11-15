theory verifythis_2021_shearsort_ShearSort_sort_all_rowsqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.int_NumOf" "Why3STD.int_Sum" "Why3STD.map_MapExt" "Why3STD.map_MapPermut" "Why3STD.matrix_Matrix"
begin
consts column :: "'a matrix \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where column'def:   "column m j i = elts m i j"
  for m :: "'a matrix"
  and j :: "int"
  and i :: "int"
consts moccf :: "'a \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where moccf'def:   "moccf x e c i = int (map_occ x (e i) (0 :: int) c)"
  for x :: "'a"
  and e :: "int \<Rightarrow> int \<Rightarrow> 'a"
  and c :: "int"
  and i :: "int"
definition mocc :: "'a \<Rightarrow> (int \<Rightarrow> int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
  where "mocc x e r c = sum (moccf x e c) (0 :: int) r" for x e r c
consts compose :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"
axiomatization where compose'def:   "compose g f x = g (f x)"
  for g :: "'b \<Rightarrow> 'c"
  and f :: "'a \<Rightarrow> 'b"
  and x :: "'a"
theorem sort_all_rows'vc:
  fixes m :: "int matrix"
  shows "let o1 :: int = rows m - (1 :: int) in ((0 :: int) \<le> o1 + (1 :: int) \<longrightarrow> ((\<forall>(i :: int). (0 :: int) \<le> i \<and> i < rows m \<longrightarrow> permut (elts m i) (elts m i) (0 :: int) (columns m)) \<and> (\<forall>(i :: int) (j :: int) (k :: int). ((0 :: int) \<le> i \<and> i < (0 :: int)) \<and> (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m \<longrightarrow> (let a :: int = elts m i j; b :: int = elts m i k in if i cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a))) \<and> (\<forall>(m1 :: int matrix). rows m1 = rows m \<and> columns m1 = columns m \<longrightarrow> (\<forall>(tid :: int). ((0 :: int) \<le> tid \<and> tid \<le> o1) \<and> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < rows m1 \<longrightarrow> permut (elts m1 i) (elts m i) (0 :: int) (columns m1)) \<and> (\<forall>(i :: int) (j :: int) (k :: int). ((0 :: int) \<le> i \<and> i < tid) \<and> (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m1 \<longrightarrow> (let a :: int = elts m1 i j; b :: int = elts m1 i k in if i cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a)) \<longrightarrow> \<not>(2 :: int) = (0 :: int) \<and> ((0 :: int) \<le> tid \<and> tid < rows m1) \<and> (\<forall>(m2 :: int matrix). rows m2 = rows m1 \<and> columns m2 = columns m1 \<longrightarrow> (\<forall>(j :: int) (k :: int). (0 :: int) \<le> j \<and> j < rows m2 \<and> ((0 :: int) \<le> k \<and> k < columns m2) \<and> \<not>j = tid \<longrightarrow> elts m2 j k = elts m1 j k) \<and> (\<forall>(j :: int) (k :: int). (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m2 \<longrightarrow> (let a :: int = elts m2 tid j; b :: int = elts m2 tid k in if tid cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a)) \<and> permut (elts m2 tid) (elts m1 tid) (0 :: int) (columns m2) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < rows m2 \<longrightarrow> permut (elts m2 i) (elts m i) (0 :: int) (columns m2)) \<and> (\<forall>(i :: int) (j :: int) (k :: int). ((0 :: int) \<le> i \<and> i < tid + (1 :: int)) \<and> (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m2 \<longrightarrow> (let a :: int = elts m2 i j; b :: int = elts m2 i k in if i cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a)))) \<and> ((\<forall>(i :: int). (0 :: int) \<le> i \<and> i < rows m1 \<longrightarrow> permut (elts m1 i) (elts m i) (0 :: int) (columns m1)) \<and> (\<forall>(i :: int) (j :: int) (k :: int). ((0 :: int) \<le> i \<and> i < o1 + (1 :: int)) \<and> (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m1 \<longrightarrow> (let a :: int = elts m1 i j; b :: int = elts m1 i k in if i cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a)) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < rows m1 \<longrightarrow> permut (elts m1 i) (elts m i) (0 :: int) (columns m1)) \<and> (\<forall>(i :: int) (j :: int) (k :: int). ((0 :: int) \<le> i \<and> i < rows m1) \<and> (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m1 \<longrightarrow> (let a :: int = elts m1 i j; b :: int = elts m1 i k in if i cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a))))) \<and> (o1 + (1 :: int) < (0 :: int) \<longrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < rows m \<longrightarrow> permut (elts m i) (elts m i) (0 :: int) (columns m)) \<and> (\<forall>(i :: int) (j :: int) (k :: int). ((0 :: int) \<le> i \<and> i < rows m) \<and> (0 :: int) \<le> j \<and> j \<le> k \<and> k < columns m \<longrightarrow> (let a :: int = elts m i j; b :: int = elts m i k in if i cmod (2 :: int) = (0 :: int) then a \<le> b else b \<le> a)))"
  sorry
end
