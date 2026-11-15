theory putnam_1979_b3 imports Complex_Main
"HOL-Computational_Algebra.Polynomial"
begin

definition putnam_1979_b3_solution :: "nat \<Rightarrow> nat" where
"putnam_1979_b3_solution \<equiv> \<lambda> n. (n - 1) div 2"
theorem putnam_1979_b3:
  fixes n :: "nat"
    and b c :: "'a::{finite, field}"
    and p :: "'a poly"
  defines "p \<equiv> [:c, b, 1:]"
  assumes hcard : "card (UNIV :: 'a set) = n"
    and nodd : "odd n"
    and hp : "irreducible p"
  shows "card {d :: 'a. irreducible (p + monom d 0)} = putnam_1979_b3_solution n"
  sorry

end
