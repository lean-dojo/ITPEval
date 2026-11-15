(*
  Statement-only formalization of the thousand-theorems corpus artifact Q220680
  (thousand-theorems__isabelle__Q220680), "Banach fixed-point theorem": a
  contraction on a complete extended metric space has a fixed point approached
  by its iterates with a geometric error bound. This file contains no proof.
*)

theory Q220680_banach_fixed_point_theorem
  imports Complex_Main
begin

type_synonym q220680_ennreal = "real option"

definition q220680_enonnegative :: "q220680_ennreal \<Rightarrow> bool" where
  "q220680_enonnegative x \<longleftrightarrow>
    (case x of None \<Rightarrow> True | Some r \<Rightarrow> 0 \<le> r)"

definition q220680_ezero :: q220680_ennreal where
  "q220680_ezero = Some 0"

definition q220680_eone :: q220680_ennreal where
  "q220680_eone = Some 1"

definition q220680_eof_real :: "real \<Rightarrow> q220680_ennreal" where
  "q220680_eof_real r = Some (max 0 r)"

definition q220680_ele ::
    "q220680_ennreal \<Rightarrow> q220680_ennreal \<Rightarrow> bool" where
  "q220680_ele x y \<longleftrightarrow>
    (case y of
      None \<Rightarrow> True
    | Some b \<Rightarrow> (case x of None \<Rightarrow> False | Some a \<Rightarrow> a \<le> b))"

definition q220680_elt ::
    "q220680_ennreal \<Rightarrow> q220680_ennreal \<Rightarrow> bool" where
  "q220680_elt x y \<longleftrightarrow> q220680_ele x y \<and> x \<noteq> y"

definition q220680_eadd ::
    "q220680_ennreal \<Rightarrow> q220680_ennreal \<Rightarrow> q220680_ennreal" where
  "q220680_eadd x y =
    (case x of
      None \<Rightarrow> None
    | Some a \<Rightarrow> (case y of None \<Rightarrow> None | Some b \<Rightarrow> Some (a + b)))"

definition q220680_emul ::
    "q220680_ennreal \<Rightarrow> q220680_ennreal \<Rightarrow> q220680_ennreal" where
  "q220680_emul x y =
    (case x of
      None \<Rightarrow>
        (case y of None \<Rightarrow> None
        | Some b \<Rightarrow> if b = 0 then q220680_ezero else None)
    | Some a \<Rightarrow>
        (case y of None \<Rightarrow> if a = 0 then q220680_ezero else None
        | Some b \<Rightarrow> Some (a * b)))"

definition q220680_esub ::
    "q220680_ennreal \<Rightarrow> q220680_ennreal \<Rightarrow> q220680_ennreal" where
  "q220680_esub x y =
    (case x of
      None \<Rightarrow> (case y of None \<Rightarrow> q220680_ezero | Some b \<Rightarrow> None)
    | Some a \<Rightarrow>
        (case y of None \<Rightarrow> q220680_ezero | Some b \<Rightarrow> Some (max 0 (a - b))))"

definition q220680_einv :: "q220680_ennreal \<Rightarrow> q220680_ennreal" where
  "q220680_einv x =
    (case x of
      None \<Rightarrow> q220680_ezero
    | Some a \<Rightarrow> if a = 0 then None else Some (inverse a))"

definition q220680_ediv ::
    "q220680_ennreal \<Rightarrow> q220680_ennreal \<Rightarrow> q220680_ennreal" where
  "q220680_ediv x y = q220680_emul x (q220680_einv y)"

primrec q220680_epow ::
    "q220680_ennreal \<Rightarrow> nat \<Rightarrow> q220680_ennreal" where
  "q220680_epow x 0 = q220680_eone"
| "q220680_epow x (Suc n) = q220680_emul (q220680_epow x n) x"

definition q220680_emetric_space ::
    "('a \<Rightarrow> 'a \<Rightarrow> q220680_ennreal) \<Rightarrow> bool" where
  "q220680_emetric_space edist \<longleftrightarrow>
    (\<forall>x y. q220680_enonnegative (edist x y)) \<and>
    (\<forall>x. edist x x = q220680_ezero) \<and>
    (\<forall>x y. edist x y = q220680_ezero \<longleftrightarrow> x = y) \<and>
    (\<forall>x y. edist x y = edist y x) \<and>
    (\<forall>x y z.
      q220680_ele (edist x z) (q220680_eadd (edist x y) (edist y z)))"

definition q220680_tendsto ::
    "('a \<Rightarrow> 'a \<Rightarrow> q220680_ennreal) \<Rightarrow>
      (nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where
  "q220680_tendsto edist u y \<longleftrightarrow>
    (\<forall>\<epsilon> :: real. 0 < \<epsilon> \<longrightarrow>
      (\<exists>N. \<forall>n \<ge> N.
        q220680_elt (edist (u n) y) (q220680_eof_real \<epsilon>)))"

definition q220680_complete ::
    "('a \<Rightarrow> 'a \<Rightarrow> q220680_ennreal) \<Rightarrow> bool" where
  "q220680_complete edist \<longleftrightarrow>
    (\<forall>u :: nat \<Rightarrow> 'a.
      (\<forall>\<epsilon> :: real. 0 < \<epsilon> \<longrightarrow>
        (\<exists>N. \<forall>m \<ge> N. \<forall>n \<ge> N.
          q220680_elt (edist (u m) (u n)) (q220680_eof_real \<epsilon>))) \<longrightarrow>
      (\<exists>y. q220680_tendsto edist u y))"

definition q220680_contracting_with ::
    "real \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> q220680_ennreal) \<Rightarrow>
      ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  "q220680_contracting_with K edist f \<longleftrightarrow>
    0 \<le> K \<and> K < 1 \<and>
    (\<forall>x y.
      q220680_ele (edist (f x) (f y))
        (q220680_emul (q220680_eof_real K) (edist x y)))"

theorem banach_fixed_point_theorem:
  fixes edist :: "'a \<Rightarrow> 'a \<Rightarrow> q220680_ennreal"
    and K :: real
    and f :: "'a \<Rightarrow> 'a"
    and x :: 'a
  assumes emetric: "q220680_emetric_space edist"
    and complete: "q220680_complete edist"
    and contracting: "q220680_contracting_with K edist f"
    and finite_displacement: "edist x (f x) \<noteq> None"
  shows "\<exists>y.
    f y = y \<and>
    q220680_tendsto edist (\<lambda>n. (f ^^ n) x) y \<and>
    (\<forall>n :: nat.
      q220680_ele (edist ((f ^^ n) x) y)
        (q220680_ediv
          (q220680_emul (edist x (f x))
            (q220680_epow (q220680_eof_real K) n))
          (q220680_esub q220680_eone (q220680_eof_real K))))"
  sorry

end
