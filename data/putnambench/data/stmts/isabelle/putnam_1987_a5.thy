theory putnam_1987_a5 imports Complex_Main
"HOL-Analysis.Cartesian_Space"
"HOL-Analysis.Derivative"
begin

definition putnam_1987_a5_solution :: "bool" where
"putnam_1987_a5_solution \<equiv> False"
theorem putnam_1987_a5:
  fixes G :: "real^2 \<Rightarrow> real^3"
    and vrepl :: "real^3 \<Rightarrow> 3 \<Rightarrow> real \<Rightarrow> real^3"
    and partderiv :: "(real^3 \<Rightarrow> real) \<Rightarrow> 3 \<Rightarrow> (real^3 \<Rightarrow> real)"
    and Fprop1 Fprop2 Fprop3 :: "(real^3 \<Rightarrow> real)^3 \<Rightarrow> bool"
  defines "G \<equiv> \<lambda> v :: real^2. vector [-v$2 / ((v$1)^2 + 4*(v$2)^2), v$1 / ((v$1)^2 + 4*(v$2)^2), 0]"
    and "vrepl \<equiv> \<lambda> (v :: real^3) (i :: 3) (vi :: real). \<chi> j :: 3. if j = i then vi else v$j"
    and "partderiv \<equiv> \<lambda> (Fi :: real^3 \<Rightarrow> real) (j :: 3). \<lambda> v :: real^3. deriv (\<lambda> vj :: real. Fi (vrepl v j vj)) (v$j)"
    and "Fprop1 \<equiv> \<lambda> F :: (real^3 \<Rightarrow> real)^3.
      (\<forall> i :: 3. \<forall> j :: 3. \<forall> v \<noteq> 0.
        (\<lambda> vj :: real. (F$i) (vrepl v j vj)) differentiable at (v$j)) \<and>
      (\<forall> i :: 3. \<forall> j :: 3.
        continuous_on (UNIV - {0}) (partderiv (F$i) j))"
    and "Fprop2 \<equiv> \<lambda> F :: (real^3 \<Rightarrow> real)^3. \<forall> v \<noteq> 0. (vector [(partderiv (F$3) 2 - partderiv (F$2) 3) v, (partderiv (F$1) 3 - partderiv (F$3) 1) v, (partderiv (F$2) 1 - partderiv (F$1) 2) v] :: real^3) = 0"
    and "Fprop3 \<equiv> \<lambda> F :: (real^3 \<Rightarrow> real)^3. \<forall> x y :: real.
      x \<noteq> 0 \<or> y \<noteq> 0 \<longrightarrow>
      (\<chi> i :: 3. (F$i) (vector [x, y, 0])) = G (vector [x, y])"
  shows "(\<exists> F :: (real^3 \<Rightarrow> real)^3. Fprop1 F \<and> Fprop2 F \<and> Fprop3 F) \<longleftrightarrow> putnam_1987_a5_solution"
  sorry

end
