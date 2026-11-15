(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q3007384 (thousand-theorems__isabelle__Q3007384), "Post's theorem":
  on any primitively codable carrier, a predicate is computable exactly when
  it and its complement are recursively enumerable. This file contains no
  proof.
*)

theory Q3007384_post_s_theorem
  imports Main
begin

definition q3007384_triangle :: "nat \<Rightarrow> nat" where
  "q3007384_triangle n = (n * Suc n) div 2"

definition q3007384_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q3007384_pair m n = q3007384_triangle (m + n) + m"

definition q3007384_unpair :: "nat \<Rightarrow> nat \<times> nat" where
  "q3007384_unpair n =
    (SOME p. q3007384_pair (fst p) (snd p) = n)"

fun q3007384_prec_total ::
    "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat" where
  "q3007384_prec_total f g z 0 = f z"
| "q3007384_prec_total f g z (Suc n) =
    g (q3007384_pair z
      (q3007384_pair n (q3007384_prec_total f g z n)))"

inductive q3007384_primrec :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  prim_zero: "q3007384_primrec (\<lambda>_. 0)"
| prim_succ: "q3007384_primrec Suc"
| prim_left: "q3007384_primrec (\<lambda>n. fst (q3007384_unpair n))"
| prim_right: "q3007384_primrec (\<lambda>n. snd (q3007384_unpair n))"
| prim_pair:
    "q3007384_primrec f \<Longrightarrow>
      q3007384_primrec g \<Longrightarrow>
      q3007384_primrec (\<lambda>n. q3007384_pair (f n) (g n))"
| prim_comp:
    "q3007384_primrec f \<Longrightarrow>
      q3007384_primrec g \<Longrightarrow>
      q3007384_primrec (\<lambda>n. f (g n))"
| prim_prec:
    "q3007384_primrec f \<Longrightarrow>
      q3007384_primrec g \<Longrightarrow>
      q3007384_primrec
        (\<lambda>n. q3007384_prec_total f g
          (fst (q3007384_unpair n)) (snd (q3007384_unpair n)))"

fun q3007384_prec_partial ::
    "(nat \<Rightarrow> nat option) \<Rightarrow> (nat \<Rightarrow> nat option) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "q3007384_prec_partial f g z 0 = f z"
| "q3007384_prec_partial f g z (Suc n) =
    (case q3007384_prec_partial f g z n of
      None \<Rightarrow> None
    | Some i \<Rightarrow> g (q3007384_pair z (q3007384_pair n i)))"

definition q3007384_rfind ::
    "(nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat option" where
  "q3007384_rfind f a =
    (if \<exists>n.
        f (q3007384_pair a n) = Some 0 \<and>
        (\<forall>m<n. f (q3007384_pair a m) \<noteq> None)
     then Some (LEAST n.
        f (q3007384_pair a n) = Some 0 \<and>
        (\<forall>m<n. f (q3007384_pair a m) \<noteq> None))
     else None)"

inductive q3007384_partrec :: "(nat \<Rightarrow> nat option) \<Rightarrow> bool" where
  part_zero: "q3007384_partrec (\<lambda>_. Some 0)"
| part_succ: "q3007384_partrec (\<lambda>n. Some (Suc n))"
| part_left:
    "q3007384_partrec (\<lambda>n. Some (fst (q3007384_unpair n)))"
| part_right:
    "q3007384_partrec (\<lambda>n. Some (snd (q3007384_unpair n)))"
| part_pair:
    "q3007384_partrec f \<Longrightarrow>
      q3007384_partrec g \<Longrightarrow>
      q3007384_partrec
        (\<lambda>n. case f n of
          None \<Rightarrow> None
        | Some x \<Rightarrow>
            (case g n of
              None \<Rightarrow> None
            | Some y \<Rightarrow> Some (q3007384_pair x y)))"
| part_comp:
    "q3007384_partrec f \<Longrightarrow>
      q3007384_partrec g \<Longrightarrow>
      q3007384_partrec
        (\<lambda>n. case g n of None \<Rightarrow> None | Some x \<Rightarrow> f x)"
| part_prec:
    "q3007384_partrec f \<Longrightarrow>
      q3007384_partrec g \<Longrightarrow>
      q3007384_partrec
        (\<lambda>n. q3007384_prec_partial f g
          (fst (q3007384_unpair n)) (snd (q3007384_unpair n)))"
| part_rfind:
    "q3007384_partrec f \<Longrightarrow>
      q3007384_partrec (q3007384_rfind f)"

definition q3007384_primcodable ::
    "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow>
      (nat \<Rightarrow> 'a option) \<Rightarrow> bool" where
  "q3007384_primcodable A encode decode \<longleftrightarrow>
    (\<forall>a\<in>A. decode (encode a) = Some a) \<and>
    (\<forall>n a. decode n = Some a \<longrightarrow> a \<in> A) \<and>
    q3007384_primrec
      (\<lambda>n. case decode n of
        None \<Rightarrow> 0
      | Some a \<Rightarrow> if a \<in> A then Suc (encode a) else 0)"

definition q3007384_computable_pred ::
    "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow>
      (nat \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "q3007384_computable_pred A encode decode p \<longleftrightarrow>
    q3007384_partrec
      (\<lambda>n. case decode n of
        None \<Rightarrow> None
      | Some a \<Rightarrow>
          if a \<in> A then Some (if p a then 1 else 0) else None)"

definition q3007384_re_pred ::
    "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow>
      (nat \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "q3007384_re_pred A encode decode p \<longleftrightarrow>
    q3007384_partrec
      (\<lambda>n. case decode n of
        None \<Rightarrow> None
      | Some a \<Rightarrow>
          if a \<in> A \<and> p a then Some 0 else None)"

theorem q3007384_post_s_theorem:
  fixes A :: "'a set"
    and encode :: "'a \<Rightarrow> nat"
    and decode :: "nat \<Rightarrow> 'a option"
    and p :: "'a \<Rightarrow> bool"
  assumes "q3007384_primcodable A encode decode"
  shows
    "q3007384_computable_pred A encode decode p \<longleftrightarrow>
      q3007384_re_pred A encode decode p \<and>
      q3007384_re_pred A encode decode (\<lambda>a. \<not> p a)"
  sorry

end
