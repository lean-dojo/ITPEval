theory putnam_1993_b1 imports Complex_Main
begin

definition putnam_1993_b1_solution :: nat where
  "putnam_1993_b1_solution \<equiv> 3987"
(* 3987 *)
theorem putnam_1993_b1:
  fixes nallmexk :: "nat \<Rightarrow> bool"
  defines "nallmexk \<equiv> \<lambda>n::nat. n > 0 \<and>
    (\<forall>m \<in> {(0::int)<..<1993}. \<exists>k::int.
      real_of_int m / 1993 < real_of_int k / real n \<and>
      real_of_int k / real n < real_of_int (m + 1) / 1994)"
  shows "putnam_1993_b1_solution = (LEAST n. nallmexk n)"
  sorry

end
