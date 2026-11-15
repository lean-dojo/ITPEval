(*
  Statement-only formalization of thousand-theorems corpus artifact Q2379132
  (thousand-theorems__isabelle__Q2379132), "Going-up and going-down theorems".
  It states the two indexed going-up results, the prime-spectrum
  characterization of going-down, and the localized-spectrum surjectivity
  criterion. This file contains no proof.
*)

theory Q2379132_going_up_and_going_down_theorems
  imports Main
begin

record 'a q2379132_comm_ring_data =
  q2379132_zero :: 'a
  q2379132_one :: 'a
  q2379132_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  q2379132_mul :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  q2379132_neg :: "'a \<Rightarrow> 'a"

definition q2379132_is_comm_ring ::
    "'a q2379132_comm_ring_data \<Rightarrow> bool" where
  "q2379132_is_comm_ring R \<longleftrightarrow>
    (\<forall>x y z.
      q2379132_add R (q2379132_add R x y) z =
        q2379132_add R x (q2379132_add R y z)) \<and>
    (\<forall>x y. q2379132_add R x y = q2379132_add R y x) \<and>
    (\<forall>x. q2379132_add R (q2379132_zero R) x = x) \<and>
    (\<forall>x. q2379132_add R (q2379132_neg R x) x =
      q2379132_zero R) \<and>
    (\<forall>x y z.
      q2379132_mul R (q2379132_mul R x y) z =
        q2379132_mul R x (q2379132_mul R y z)) \<and>
    (\<forall>x y. q2379132_mul R x y = q2379132_mul R y x) \<and>
    (\<forall>x. q2379132_mul R (q2379132_one R) x = x) \<and>
    (\<forall>x y z.
      q2379132_mul R x (q2379132_add R y z) =
        q2379132_add R
          (q2379132_mul R x y) (q2379132_mul R x z))"

definition q2379132_is_integral_domain ::
    "'a q2379132_comm_ring_data \<Rightarrow> bool" where
  "q2379132_is_integral_domain R \<longleftrightarrow>
    q2379132_is_comm_ring R \<and>
    q2379132_zero R \<noteq> q2379132_one R \<and>
    (\<forall>x y.
      q2379132_mul R x y = q2379132_zero R \<longrightarrow>
        x = q2379132_zero R \<or> y = q2379132_zero R)"

definition q2379132_is_ring_hom ::
    "'r q2379132_comm_ring_data \<Rightarrow>
      's q2379132_comm_ring_data \<Rightarrow> ('r \<Rightarrow> 's) \<Rightarrow> bool" where
  "q2379132_is_ring_hom R S f \<longleftrightarrow>
    f (q2379132_zero R) = q2379132_zero S \<and>
    f (q2379132_one R) = q2379132_one S \<and>
    (\<forall>x y.
      f (q2379132_add R x y) = q2379132_add S (f x) (f y)) \<and>
    (\<forall>x y.
      f (q2379132_mul R x y) = q2379132_mul S (f x) (f y))"

definition q2379132_is_ideal ::
    "'a q2379132_comm_ring_data \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q2379132_is_ideal R I \<longleftrightarrow>
    q2379132_zero R \<in> I \<and>
    (\<forall>x\<in>I. \<forall>y\<in>I. q2379132_add R x y \<in> I) \<and>
    (\<forall>x\<in>I. q2379132_neg R x \<in> I) \<and>
    (\<forall>a. \<forall>x\<in>I. q2379132_mul R a x \<in> I)"

definition q2379132_is_prime_ideal ::
    "'a q2379132_comm_ring_data \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q2379132_is_prime_ideal R P \<longleftrightarrow>
    q2379132_is_ideal R P \<and>
    q2379132_one R \<notin> P \<and>
    (\<forall>x y.
      q2379132_mul R x y \<in> P \<longrightarrow> x \<in> P \<or> y \<in> P)"

fun q2379132_poly_eval ::
    "'r q2379132_comm_ring_data \<Rightarrow>
      's q2379132_comm_ring_data \<Rightarrow>
      ('r \<Rightarrow> 's) \<Rightarrow> 'r list \<Rightarrow> 's \<Rightarrow> 's" where
  "q2379132_poly_eval R S f [] x = q2379132_zero S"
| "q2379132_poly_eval R S f (c # cs) x =
    q2379132_add S (f c)
      (q2379132_mul S x (q2379132_poly_eval R S f cs x))"

definition q2379132_is_integral_extension ::
    "'r q2379132_comm_ring_data \<Rightarrow>
      's q2379132_comm_ring_data \<Rightarrow> ('r \<Rightarrow> 's) \<Rightarrow> bool" where
  "q2379132_is_integral_extension R S f \<longleftrightarrow>
    (\<forall>x. \<exists>coeffs :: 'r list.
      coeffs \<noteq> [] \<and>
      last coeffs = q2379132_one R \<and>
      q2379132_poly_eval R S f coeffs x = q2379132_zero S)"

definition q2379132_contraction ::
    "('r \<Rightarrow> 's) \<Rightarrow> 's set \<Rightarrow> 'r set" where
  "q2379132_contraction f Q = {x. f x \<in> Q}"

definition q2379132_has_going_down ::
    "'r q2379132_comm_ring_data \<Rightarrow>
      's q2379132_comm_ring_data \<Rightarrow> ('r \<Rightarrow> 's) \<Rightarrow> bool" where
  "q2379132_has_going_down R S f \<longleftrightarrow>
    (\<forall>p q Q.
      q2379132_is_prime_ideal R p \<and>
      q2379132_is_prime_ideal R q \<and>
      q2379132_is_prime_ideal S Q \<and>
      p \<subseteq> q \<and> q2379132_contraction f Q = q
      \<longrightarrow>
      (\<exists>P.
        q2379132_is_prime_ideal S P \<and>
        P \<subseteq> Q \<and> q2379132_contraction f P = p))"

definition q2379132_generalizing_prime_spectrum_comap ::
    "'r q2379132_comm_ring_data \<Rightarrow>
      's q2379132_comm_ring_data \<Rightarrow> ('r \<Rightarrow> 's) \<Rightarrow> bool" where
  "q2379132_generalizing_prime_spectrum_comap R S f \<longleftrightarrow>
    (\<forall>Q p.
      q2379132_is_prime_ideal S Q \<and>
      q2379132_is_prime_ideal R p \<and>
      p \<subseteq> q2379132_contraction f Q
      \<longrightarrow>
      (\<exists>P.
        q2379132_is_prime_ideal S P \<and>
        P \<subseteq> Q \<and> q2379132_contraction f P = p))"

(*
  Under the canonical correspondence for localization at a prime, the prime
  spectrum of R_p is the set of prime ideals of R contained in p. Thus this
  predicate is exactly surjectivity of Spec(S_Q) -> Spec(R_{f^-1 Q}).
*)
definition q2379132_local_prime_spectrum_comap_surjective ::
    "'r q2379132_comm_ring_data \<Rightarrow>
      's q2379132_comm_ring_data \<Rightarrow>
      ('r \<Rightarrow> 's) \<Rightarrow> 's set \<Rightarrow> bool" where
  "q2379132_local_prime_spectrum_comap_surjective R S f Q \<longleftrightarrow>
    (\<forall>p.
      q2379132_is_prime_ideal R p \<and>
      p \<subseteq> q2379132_contraction f Q
      \<longrightarrow>
      (\<exists>P.
        q2379132_is_prime_ideal S P \<and>
        P \<subseteq> Q \<and> q2379132_contraction f P = p))"

theorem q2379132_exists_ideal_over_prime:
  fixes R :: "'r q2379132_comm_ring_data"
    and S :: "'s q2379132_comm_ring_data"
    and f :: "'r \<Rightarrow> 's"
    and P :: "'r set"
  assumes "q2379132_is_comm_ring R"
    and "q2379132_is_integral_domain S"
    and "q2379132_is_ring_hom R S f"
    and "q2379132_is_integral_extension R S f"
    and "q2379132_is_prime_ideal R P"
    and "{x. f x = q2379132_zero S} \<subseteq> P"
  shows "\<exists>Q :: 's set.
    q2379132_is_prime_ideal S Q \<and>
    q2379132_contraction f Q = P"
  sorry

theorem q2379132_exists_ideal_over_prime_above:
  fixes R :: "'r q2379132_comm_ring_data"
    and S :: "'s q2379132_comm_ring_data"
    and f :: "'r \<Rightarrow> 's"
    and P :: "'r set"
    and I :: "'s set"
  assumes "q2379132_is_comm_ring R"
    and "q2379132_is_comm_ring S"
    and "q2379132_is_ring_hom R S f"
    and "q2379132_is_integral_extension R S f"
    and "q2379132_is_prime_ideal R P"
    and "q2379132_is_prime_ideal S I"
    and "q2379132_contraction f I \<subseteq> P"
  shows "\<exists>Q :: 's set.
    I \<subseteq> Q \<and>
    q2379132_is_prime_ideal S Q \<and>
    q2379132_contraction f Q = P"
  sorry

theorem q2379132_going_down_iff_generalizing_prime_spectrum_comap:
  fixes R :: "'r q2379132_comm_ring_data"
    and S :: "'s q2379132_comm_ring_data"
    and f :: "'r \<Rightarrow> 's"
  assumes "q2379132_is_comm_ring R"
    and "q2379132_is_comm_ring S"
    and "q2379132_is_ring_hom R S f"
  shows "q2379132_has_going_down R S f \<longleftrightarrow>
    q2379132_generalizing_prime_spectrum_comap R S f"
  sorry

theorem q2379132_has_going_down_of_local_prime_spectrum_comap_surjective:
  fixes R :: "'r q2379132_comm_ring_data"
    and S :: "'s q2379132_comm_ring_data"
    and f :: "'r \<Rightarrow> 's"
  assumes "q2379132_is_comm_ring R"
    and "q2379132_is_comm_ring S"
    and "q2379132_is_ring_hom R S f"
    and "\<forall>Q.
      q2379132_is_prime_ideal S Q \<longrightarrow>
      q2379132_local_prime_spectrum_comap_surjective R S f Q"
  shows "q2379132_has_going_down R S f"
  sorry

end
