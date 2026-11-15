(*
  Statement-only formalization of thousand-theorems corpus artifact Q776578
  (thousand-theorems__isabelle__Q776578), "Artin–Wedderburn theorem": every
  semisimple algebra is isomorphic, over its commutative semiring of scalars,
  to a finite product of positive-size matrix algebras over division algebras.
  This file contains no proof.
*)

theory Q776578_artin_wedderburn_theorem
  imports Main
begin

type_synonym 'r q776578_end = "'r \<Rightarrow> 'r"
type_synonym 'r q776578_matrix_product =
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'r q776578_end"

definition q776578_comm_semiring where
  "q776578_comm_semiring C z one add mul \<longleftrightarrow>
    z \<in> C \<and>
    one \<in> C \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. add x y \<in> C) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. mul x y \<in> C) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      add (add x y) w = add x (add y w)) \<and>
    (\<forall>x\<in>C. add z x = x) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. add x y = add y x) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      mul (mul x y) w = mul x (mul y w)) \<and>
    (\<forall>x\<in>C. mul one x = x \<and> mul x one = x) \<and>
    (\<forall>x\<in>C. mul z x = z \<and> mul x z = z) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. mul x y = mul y x) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      mul x (add y w) = add (mul x y) (mul x w)) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      mul (add x y) w = add (mul x w) (mul y w))"

definition q776578_ring where
  "q776578_ring C z one add neg mul \<longleftrightarrow>
    z \<in> C \<and>
    one \<in> C \<and>
    (\<forall>x\<in>C. neg x \<in> C) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. add x y \<in> C) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. mul x y \<in> C) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      add (add x y) w = add x (add y w)) \<and>
    (\<forall>x\<in>C. add z x = x) \<and>
    (\<forall>x\<in>C. add (neg x) x = z) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. add x y = add y x) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      mul (mul x y) w = mul x (mul y w)) \<and>
    (\<forall>x\<in>C. mul one x = x \<and> mul x one = x) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      mul x (add y w) = add (mul x y) (mul x w)) \<and>
    (\<forall>x\<in>C. \<forall>y\<in>C. \<forall>w\<in>C.
      mul (add x y) w = add (mul x w) (mul y w))"

definition q776578_algebra_map where
  "q776578_algebra_map KC kz ko kadd kmul RC rz ro radd rmul alg \<longleftrightarrow>
    (\<forall>a\<in>KC. alg a \<in> RC) \<and>
    alg kz = rz \<and>
    alg ko = ro \<and>
    (\<forall>a\<in>KC. \<forall>b\<in>KC. alg (kadd a b) = radd (alg a) (alg b)) \<and>
    (\<forall>a\<in>KC. \<forall>b\<in>KC. alg (kmul a b) = rmul (alg a) (alg b)) \<and>
    (\<forall>a\<in>KC. \<forall>x\<in>RC. rmul (alg a) x = rmul x (alg a))"

definition q776578_left_ideal where
  "q776578_left_ideal RC rz radd rneg rmul I \<longleftrightarrow>
    I \<subseteq> RC \<and>
    rz \<in> I \<and>
    (\<forall>x\<in>I. rneg x \<in> I) \<and>
    (\<forall>x\<in>I. \<forall>y\<in>I. radd x y \<in> I) \<and>
    (\<forall>a\<in>RC. \<forall>x\<in>I. rmul a x \<in> I)"

definition q776578_semisimple_ring where
  "q776578_semisimple_ring RC rz radd rneg rmul \<longleftrightarrow>
    (\<forall>I. q776578_left_ideal RC rz radd rneg rmul I \<longrightarrow>
      (\<exists>J. q776578_left_ideal RC rz radd rneg rmul J \<and>
        I \<inter> J = {rz} \<and>
        (\<forall>x\<in>RC. \<exists>y\<in>I. \<exists>w\<in>J. x = radd y w)))"

definition q776578_division_ring where
  "q776578_division_ring C z one add neg mul \<longleftrightarrow>
    q776578_ring C z one add neg mul \<and>
    z \<noteq> one \<and>
    (\<forall>x\<in>C. x \<noteq> z \<longrightarrow>
      (\<exists>y\<in>C. mul x y = one \<and> mul y x = one))"

primrec q776578_sum where
  "q776578_sum z add f 0 = z"
| "q776578_sum z add f (Suc n) =
    add (q776578_sum z add f n) (f n)"

definition q776578_matrix_product_carrier ::
    "nat \<Rightarrow> (nat \<Rightarrow> 'v set) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
      (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'v) set" where
  "q776578_matrix_product_carrier n D d =
    {A. \<forall>i p q.
      if i < n \<and> p < d i \<and> q < d i
      then A i p q \<in> D i
      else A i p q = undefined}"

definition q776578_is_algebra_equiv where
  "q776578_is_algebra_equiv
      KC kz ko kadd kmul
      RC rz ro radd rneg rmul alg
      n D Dz Do Dadd Dneg Dmul Dalg d phi \<longleftrightarrow>
    bij_betw phi RC (q776578_matrix_product_carrier n D d) \<and>
    (\<forall>i<n. \<forall>p<d i. \<forall>q<d i.
      phi rz i p q = Dz i) \<and>
    (\<forall>i<n. \<forall>p<d i. \<forall>q<d i.
      phi ro i p q = (if p = q then Do i else Dz i)) \<and>
    (\<forall>x\<in>RC. \<forall>y\<in>RC. \<forall>i<n. \<forall>p<d i. \<forall>q<d i.
      phi (radd x y) i p q = Dadd i (phi x i p q) (phi y i p q)) \<and>
    (\<forall>x\<in>RC. \<forall>i<n. \<forall>p<d i. \<forall>q<d i.
      phi (rneg x) i p q = Dneg i (phi x i p q)) \<and>
    (\<forall>x\<in>RC. \<forall>y\<in>RC. \<forall>i<n. \<forall>p<d i. \<forall>q<d i.
      phi (rmul x y) i p q =
        q776578_sum (Dz i) (Dadd i)
          (\<lambda>k. Dmul i (phi x i p k) (phi y i k q)) (d i)) \<and>
    (\<forall>a\<in>KC. \<forall>i<n. \<forall>p<d i. \<forall>q<d i.
      phi (alg a) i p q = (if p = q then Dalg i a else Dz i))"

theorem q776578_artin_wedderburn_theorem:
  fixes KC :: "'k set"
    and kz ko :: "'k"
    and kadd kmul :: "'k \<Rightarrow> 'k \<Rightarrow> 'k"
    and RC :: "'r set"
    and rz ro :: "'r"
    and radd rmul :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
    and rneg :: "'r \<Rightarrow> 'r"
    and alg :: "'k \<Rightarrow> 'r"
  assumes "q776578_comm_semiring KC kz ko kadd kmul"
    and "q776578_ring RC rz ro radd rneg rmul"
    and "q776578_algebra_map KC kz ko kadd kmul RC rz ro radd rmul alg"
    and "q776578_semisimple_ring RC rz radd rneg rmul"
  shows "\<exists>(n :: nat)
      (D :: nat \<Rightarrow> ('r q776578_end) set)
      (Dz :: nat \<Rightarrow> 'r q776578_end)
      (Do :: nat \<Rightarrow> 'r q776578_end)
      (Dadd :: nat \<Rightarrow>
        'r q776578_end \<Rightarrow> 'r q776578_end \<Rightarrow> 'r q776578_end)
      (Dmul :: nat \<Rightarrow>
        'r q776578_end \<Rightarrow> 'r q776578_end \<Rightarrow> 'r q776578_end)
      (Dneg :: nat \<Rightarrow> 'r q776578_end \<Rightarrow> 'r q776578_end)
      (Dalg :: nat \<Rightarrow> 'k \<Rightarrow> 'r q776578_end)
      (d :: nat \<Rightarrow> nat)
      (phi :: 'r \<Rightarrow> 'r q776578_matrix_product).
    (\<forall>i<n.
      q776578_division_ring
        (D i) (Dz i) (Do i) (Dadd i) (Dneg i) (Dmul i) \<and>
      q776578_algebra_map
        KC kz ko kadd kmul
        (D i) (Dz i) (Do i) (Dadd i) (Dmul i) (Dalg i)) \<and>
    (\<forall>i<n. 0 < d i) \<and>
    q776578_is_algebra_equiv
      KC kz ko kadd kmul
      RC rz ro radd rneg rmul alg
      n D Dz Do Dadd Dneg Dmul Dalg d phi"
  sorry

end
