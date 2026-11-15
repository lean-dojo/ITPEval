(*
  Statement-only formalization of thousand-theorems corpus artifact Q1065257,
  "Squeeze theorem": for functions into a preordered space with its order
  topology, eventual lower and upper bounds converging to the same point force
  the bounded function to converge there. This file contains no proof.
*)

theory Q1065257_squeeze_theorem
  imports "HOL.Topological_Spaces"
begin

locale preorder_order_topology =
  fixes le :: "'a::topological_space \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
    and lt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes le_refl: "\<And>x. x \<preceq> x"
    and le_trans:
      "\<And>x y z. x \<preceq> y \<Longrightarrow> y \<preceq> z \<Longrightarrow> x \<preceq> z"
    and lt_iff_le_not_le:
      "\<And>x y. x \<prec> y \<longleftrightarrow> x \<preceq> y \<and> \<not> y \<preceq> x"
    and open_generated_order:
      "open =
        generate_topology
          (range (\<lambda>a. {b. a \<prec> b}) \<union> range (\<lambda>a. {b. b \<prec> a}))"
begin

theorem squeeze_theorem:
  fixes f g h :: "'b \<Rightarrow> 'a"
    and net :: "'b filter"
    and a :: "'a"
  assumes "(g \<longlongrightarrow> a) net"
    and "(h \<longlongrightarrow> a) net"
    and "eventually (\<lambda>x. g x \<preceq> f x) net"
    and "eventually (\<lambda>x. f x \<preceq> h x) net"
  shows "(f \<longlongrightarrow> a) net"
  sorry

end

end
