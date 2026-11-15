theory putnam_2019_a5 imports Complex_Main
"HOL-Computational_Algebra.Polynomial"
"HOL-Library.Cardinality"
begin

definition putnam_2019_a5_solution :: "nat \<Rightarrow> nat" where
  "putnam_2019_a5_solution \<equiv> (\<lambda>p. (p - 1) div 2)"
(* (\<lambda>p::nat. (p - 1) div 2) *)
theorem putnam_2019_a5:
  fixes p :: nat
  and ppind :: "nat \<Rightarrow> 'p::{comm_ring_1, finite}"
  and q :: "'p poly"
  and a :: "nat \<Rightarrow> 'p"
  and npoly :: "nat \<Rightarrow> ('p poly)"
  and ndiv :: "nat \<Rightarrow> bool"
  assumes podd: "odd p"
  and pprime: "prime p"
  and ppcard: "CARD('p) = p"
  and hppind: "ppind ` {0..<p} = UNIV"
  and ppadd: "ppind 0 = 0 \<and>
    (\<forall>i::nat\<in>{0..<p}. \<forall>j::nat\<in>{0..<p}.
      ppind i + ppind j = ppind ((i + j) mod p))"
  and ppmult: "ppind 1 = 1 \<and>
    (\<forall>i::nat\<in>{0..<p}. \<forall>j::nat\<in>{0..<p}.
      ppind i * ppind j = ppind ((i * j) mod p))"
  and hq: "\<forall>k::nat. coeff q k = a k"
  and ha0: "a 0 = 0 \<and> (\<forall>k::nat\<ge>p. a k = 0)"
  and haother: "\<forall>k::nat\<in>{1..<p}.
    a k = ppind ((k ^ ((p - 1) div 2)) mod p)"
  and hnpoly: "\<forall>n::nat. npoly n = (monom 1 1 - 1)^n"
  and hndiv: "\<forall>n::nat. ndiv n = ((npoly n) dvd q)"
  shows "ndiv (putnam_2019_a5_solution p) \<and>
    (\<forall>n::nat. ndiv n \<longrightarrow> n \<le> putnam_2019_a5_solution p)"
  sorry

end
