(*
  Statement-only formalization of thousand-theorems corpus artifact Q208416
  (thousand-theorems__isabelle__Q208416), "Independence of the continuum
  hypothesis": the Flypitch first-order sentence expressing CH and its
  negation are both unprovable from its formulation of ZFC. This file contains
  no proof.
*)

theory Q208416_independence_of_the_continuum_hypothesis
  imports Main
begin

datatype q208416_term =
    Q208416_Var nat
  | Q208416_Empty
  | Q208416_Pair q208416_term q208416_term
  | Q208416_Omega
  | Q208416_Powerset q208416_term
  | Q208416_Union q208416_term

datatype q208416_formula =
    Q208416_False
  | Q208416_Eq q208416_term q208416_term
  | Q208416_Mem q208416_term q208416_term
  | Q208416_Imp q208416_formula q208416_formula
  | Q208416_All q208416_formula

definition q208416_not :: "q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_not A = Q208416_Imp A Q208416_False"

definition q208416_and ::
    "q208416_formula \<Rightarrow> q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_and A B =
    q208416_not (Q208416_Imp A (q208416_not B))"

definition q208416_or ::
    "q208416_formula \<Rightarrow> q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_or A B = Q208416_Imp (q208416_not A) B"

definition q208416_iff ::
    "q208416_formula \<Rightarrow> q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_iff A B =
    q208416_and (Q208416_Imp A B) (Q208416_Imp B A)"

definition q208416_ex :: "q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_ex A = q208416_not (Q208416_All (q208416_not A))"

primrec q208416_lift_term_at ::
    "q208416_term \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> q208416_term" where
  "q208416_lift_term_at (Q208416_Var k) n m =
    Q208416_Var (if m \<le> k then k + n else k)"
| "q208416_lift_term_at Q208416_Empty n m = Q208416_Empty"
| "q208416_lift_term_at (Q208416_Pair s t) n m =
    Q208416_Pair
      (q208416_lift_term_at s n m)
      (q208416_lift_term_at t n m)"
| "q208416_lift_term_at Q208416_Omega n m = Q208416_Omega"
| "q208416_lift_term_at (Q208416_Powerset t) n m =
    Q208416_Powerset (q208416_lift_term_at t n m)"
| "q208416_lift_term_at (Q208416_Union t) n m =
    Q208416_Union (q208416_lift_term_at t n m)"

primrec q208416_subst_term ::
    "q208416_term \<Rightarrow> q208416_term \<Rightarrow> nat \<Rightarrow> q208416_term" where
  "q208416_subst_term (Q208416_Var k) s n =
    (if k < n then Q208416_Var k
     else if k = n then q208416_lift_term_at s n 0
     else Q208416_Var (k - 1))"
| "q208416_subst_term Q208416_Empty s n = Q208416_Empty"
| "q208416_subst_term (Q208416_Pair t u) s n =
    Q208416_Pair
      (q208416_subst_term t s n)
      (q208416_subst_term u s n)"
| "q208416_subst_term Q208416_Omega s n = Q208416_Omega"
| "q208416_subst_term (Q208416_Powerset t) s n =
    Q208416_Powerset (q208416_subst_term t s n)"
| "q208416_subst_term (Q208416_Union t) s n =
    Q208416_Union (q208416_subst_term t s n)"

primrec q208416_lift_formula_at ::
    "q208416_formula \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> q208416_formula" where
  "q208416_lift_formula_at Q208416_False n m = Q208416_False"
| "q208416_lift_formula_at (Q208416_Eq s t) n m =
    Q208416_Eq
      (q208416_lift_term_at s n m)
      (q208416_lift_term_at t n m)"
| "q208416_lift_formula_at (Q208416_Mem s t) n m =
    Q208416_Mem
      (q208416_lift_term_at s n m)
      (q208416_lift_term_at t n m)"
| "q208416_lift_formula_at (Q208416_Imp A B) n m =
    Q208416_Imp
      (q208416_lift_formula_at A n m)
      (q208416_lift_formula_at B n m)"
| "q208416_lift_formula_at (Q208416_All A) n m =
    Q208416_All (q208416_lift_formula_at A n (Suc m))"

primrec q208416_subst_formula ::
    "q208416_formula \<Rightarrow> q208416_term \<Rightarrow> nat \<Rightarrow>
      q208416_formula" where
  "q208416_subst_formula Q208416_False s n = Q208416_False"
| "q208416_subst_formula (Q208416_Eq t u) s n =
    Q208416_Eq
      (q208416_subst_term t s n)
      (q208416_subst_term u s n)"
| "q208416_subst_formula (Q208416_Mem t u) s n =
    Q208416_Mem
      (q208416_subst_term t s n)
      (q208416_subst_term u s n)"
| "q208416_subst_formula (Q208416_Imp A B) s n =
    Q208416_Imp
      (q208416_subst_formula A s n)
      (q208416_subst_formula B s n)"
| "q208416_subst_formula (Q208416_All A) s n =
    Q208416_All (q208416_subst_formula A s (Suc n))"

primrec q208416_term_bounded :: "nat \<Rightarrow> q208416_term \<Rightarrow> bool" where
  "q208416_term_bounded n (Q208416_Var k) = (k < n)"
| "q208416_term_bounded n Q208416_Empty = True"
| "q208416_term_bounded n (Q208416_Pair s t) =
    (q208416_term_bounded n s \<and> q208416_term_bounded n t)"
| "q208416_term_bounded n Q208416_Omega = True"
| "q208416_term_bounded n (Q208416_Powerset t) =
    q208416_term_bounded n t"
| "q208416_term_bounded n (Q208416_Union t) =
    q208416_term_bounded n t"

primrec q208416_formula_bounded ::
    "nat \<Rightarrow> q208416_formula \<Rightarrow> bool" where
  "q208416_formula_bounded n Q208416_False = True"
| "q208416_formula_bounded n (Q208416_Eq s t) =
    (q208416_term_bounded n s \<and> q208416_term_bounded n t)"
| "q208416_formula_bounded n (Q208416_Mem s t) =
    (q208416_term_bounded n s \<and> q208416_term_bounded n t)"
| "q208416_formula_bounded n (Q208416_Imp A B) =
    (q208416_formula_bounded n A \<and> q208416_formula_bounded n B)"
| "q208416_formula_bounded n (Q208416_All A) =
    q208416_formula_bounded (Suc n) A"

primrec q208416_alls :: "nat \<Rightarrow> q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_alls 0 A = A"
| "q208416_alls (Suc n) A = Q208416_All (q208416_alls n A)"

definition q208416_subset ::
    "q208416_term \<Rightarrow> q208416_term \<Rightarrow> q208416_formula" where
  "q208416_subset s t =
    Q208416_All
      (Q208416_Imp
        (Q208416_Mem
          (Q208416_Var 0) (q208416_lift_term_at s 1 0))
        (Q208416_Mem
          (Q208416_Var 0) (q208416_lift_term_at t 1 0)))"

definition q208416_transitive_formula :: q208416_formula where
  "q208416_transitive_formula =
    Q208416_All
      (Q208416_Imp
        (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
        (q208416_subset (Q208416_Var 0) (Q208416_Var 1)))"

definition q208416_epsilon_trichotomy_formula :: q208416_formula where
  "q208416_epsilon_trichotomy_formula =
    Q208416_All
      (Q208416_Imp
        (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
        (Q208416_All
          (Q208416_Imp
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 2))
            (q208416_or
              (q208416_or
                (Q208416_Eq (Q208416_Var 1) (Q208416_Var 0))
                (Q208416_Mem (Q208416_Var 1) (Q208416_Var 0)))
              (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))))))"

definition q208416_epsilon_well_founded_formula :: q208416_formula where
  "q208416_epsilon_well_founded_formula =
    Q208416_All
      (Q208416_Imp
        (q208416_subset (Q208416_Var 0) (Q208416_Var 1))
        (Q208416_Imp
          (q208416_not
            (Q208416_Eq (Q208416_Var 0) Q208416_Empty))
          (q208416_ex
            (q208416_and
              (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
              (Q208416_All
                (Q208416_Imp
                  (Q208416_Mem
                    (Q208416_Var 0) (Q208416_Var 2))
                  (q208416_not
                    (Q208416_Mem
                      (Q208416_Var 0) (Q208416_Var 1)))))))))"

definition q208416_ordinal_formula :: q208416_formula where
  "q208416_ordinal_formula =
    q208416_and
      (q208416_and
        q208416_epsilon_trichotomy_formula
        q208416_epsilon_well_founded_formula)
      q208416_transitive_formula"

definition q208416_axiom_emptyset :: q208416_formula where
  "q208416_axiom_emptyset =
    Q208416_All
      (q208416_not
        (Q208416_Mem (Q208416_Var 0) Q208416_Empty))"

definition q208416_axiom_pair :: q208416_formula where
  "q208416_axiom_pair =
    Q208416_All (Q208416_All (Q208416_All (Q208416_All
      (q208416_iff
        (Q208416_Eq
          (Q208416_Pair (Q208416_Var 3) (Q208416_Var 2))
          (Q208416_Pair (Q208416_Var 1) (Q208416_Var 0)))
        (q208416_and
          (Q208416_Eq (Q208416_Var 3) (Q208416_Var 1))
          (Q208416_Eq (Q208416_Var 2) (Q208416_Var 0)))))))"

definition q208416_axiom_extensionality :: q208416_formula where
  "q208416_axiom_extensionality =
    Q208416_All (Q208416_All
      (Q208416_Imp
        (Q208416_All
          (q208416_iff
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 2))
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))))
        (Q208416_Eq (Q208416_Var 1) (Q208416_Var 0))))"

definition q208416_axiom_union :: q208416_formula where
  "q208416_axiom_union =
    Q208416_All (Q208416_All
      (q208416_iff
        (Q208416_Mem
          (Q208416_Var 0) (Q208416_Union (Q208416_Var 1)))
        (q208416_ex
          (q208416_and
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 2))
            (Q208416_Mem (Q208416_Var 1) (Q208416_Var 0))))))"

definition q208416_axiom_powerset :: q208416_formula where
  "q208416_axiom_powerset =
    Q208416_All (Q208416_All
      (q208416_iff
        (Q208416_Mem
          (Q208416_Var 0) (Q208416_Powerset (Q208416_Var 1)))
        (Q208416_All
          (Q208416_Imp
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 2))))))"

definition q208416_axiom_infinity :: q208416_formula where
  "q208416_axiom_infinity =
    q208416_and
      (q208416_and
        (Q208416_Mem Q208416_Empty Q208416_Omega)
        (Q208416_All
          (Q208416_Imp
            (Q208416_Mem (Q208416_Var 0) Q208416_Omega)
            (q208416_ex
              (q208416_and
                (Q208416_Mem (Q208416_Var 0) Q208416_Omega)
                (Q208416_Mem
                  (Q208416_Var 1) (Q208416_Var 0)))))))
      (q208416_and
        (q208416_ex
          (q208416_and
            q208416_ordinal_formula
            (Q208416_Eq Q208416_Omega (Q208416_Var 0))))
        (Q208416_All
          (Q208416_Imp
            q208416_ordinal_formula
            (Q208416_Imp
              (q208416_and
                (Q208416_Mem Q208416_Empty (Q208416_Var 0))
                (Q208416_All
                  (Q208416_Imp
                    (Q208416_Mem
                      (Q208416_Var 0) (Q208416_Var 1))
                    (q208416_ex
                      (q208416_and
                        (Q208416_Mem
                          (Q208416_Var 0) (Q208416_Var 2))
                        (Q208416_Mem
                          (Q208416_Var 1) (Q208416_Var 0)))))))
              (q208416_subset
                Q208416_Omega (Q208416_Var 0))))))"

definition q208416_axiom_regularity :: q208416_formula where
  "q208416_axiom_regularity =
    Q208416_All
      (Q208416_Imp
        (q208416_not
          (Q208416_Eq (Q208416_Var 0) Q208416_Empty))
        (q208416_ex
          (q208416_and
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
            (Q208416_All
              (Q208416_Imp
                (Q208416_Mem (Q208416_Var 0) (Q208416_Var 2))
                (q208416_not
                  (Q208416_Mem
                    (Q208416_Var 0) (Q208416_Var 1))))))))"

definition q208416_zorns_lemma :: q208416_formula where
  "q208416_zorns_lemma =
    Q208416_All
      (Q208416_Imp
        (q208416_not
          (Q208416_Eq (Q208416_Var 0) Q208416_Empty))
        (Q208416_Imp
          (Q208416_All
            (Q208416_Imp
              (q208416_and
                (q208416_subset
                  (Q208416_Var 0) (Q208416_Var 1))
                (Q208416_All (Q208416_All
                  (Q208416_Imp
                    (q208416_and
                      (Q208416_Mem
                        (Q208416_Var 1) (Q208416_Var 2))
                      (Q208416_Mem
                        (Q208416_Var 0) (Q208416_Var 2)))
                    (q208416_or
                      (q208416_subset
                        (Q208416_Var 1) (Q208416_Var 0))
                      (q208416_subset
                        (Q208416_Var 0) (Q208416_Var 1)))))))
              (Q208416_Mem
                (Q208416_Union (Q208416_Var 0))
                (Q208416_Var 1))))
          (q208416_ex
            (q208416_and
              (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
              (Q208416_All
                (Q208416_Imp
                  (Q208416_Mem
                    (Q208416_Var 0) (Q208416_Var 2))
                  (Q208416_Imp
                    (q208416_subset
                      (Q208416_Var 1) (Q208416_Var 0))
                    (Q208416_Eq
                      (Q208416_Var 1) (Q208416_Var 0)))))))))"

definition q208416_collection_axiom ::
    "nat \<Rightarrow> q208416_formula \<Rightarrow> q208416_formula" where
  "q208416_collection_axiom n phi =
    q208416_alls (Suc n)
      (Q208416_Imp
        (Q208416_All
          (Q208416_Imp
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 1))
            (q208416_ex (q208416_lift_formula_at phi 1 2))))
        (q208416_ex
          (q208416_and
            (Q208416_All
              (Q208416_Imp
                (Q208416_Mem
                  (Q208416_Var 0) (Q208416_Var 2))
                (q208416_ex
                  (q208416_and
                    (Q208416_Mem
                      (Q208416_Var 0) (Q208416_Var 2))
                    (q208416_lift_formula_at phi 2 2)))))
            (Q208416_All
              (Q208416_Imp
                (Q208416_Mem
                  (Q208416_Var 0) (Q208416_Var 1))
                (q208416_ex
                  (q208416_and
                    (Q208416_Mem
                      (Q208416_Var 0) (Q208416_Var 3))
                    (q208416_subst_formula
                      (q208416_lift_formula_at phi 3 2)
                      (Q208416_Var 1) 0))))))))"

definition q208416_ZFC :: "q208416_formula set" where
  "q208416_ZFC =
    {q208416_axiom_emptyset,
     q208416_axiom_pair,
     q208416_axiom_extensionality,
     q208416_axiom_union,
     q208416_axiom_powerset,
     q208416_axiom_infinity,
     q208416_axiom_regularity,
     q208416_zorns_lemma}
    \<union>
    {A. \<exists>n phi.
      q208416_formula_bounded (n + 2) phi \<and>
      A = q208416_collection_axiom n phi}"

definition q208416_is_func_formula :: q208416_formula where
  "q208416_is_func_formula =
    Q208416_All (Q208416_All (Q208416_All (Q208416_All
      (Q208416_Imp
        (q208416_and
          (Q208416_Mem
            (Q208416_Pair (Q208416_Var 3) (Q208416_Var 1))
            (Q208416_Var 4))
          (Q208416_Mem
            (Q208416_Pair (Q208416_Var 2) (Q208416_Var 0))
            (Q208416_Var 4)))
        (Q208416_Imp
          (Q208416_Eq (Q208416_Var 3) (Q208416_Var 2))
          (Q208416_Eq (Q208416_Var 1) (Q208416_Var 0)))))))"

definition q208416_is_total_reversed_formula :: q208416_formula where
  "q208416_is_total_reversed_formula =
    Q208416_All
      (Q208416_Imp
        (Q208416_Mem (Q208416_Var 0) (Q208416_Var 2))
        (q208416_ex
          (q208416_and
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 4))
            (Q208416_Mem
              (Q208416_Pair
                (Q208416_Var 1) (Q208416_Var 0))
              (Q208416_Var 2)))))"

definition q208416_is_reversed_function_formula :: q208416_formula where
  "q208416_is_reversed_function_formula =
    q208416_and
      q208416_is_func_formula
      q208416_is_total_reversed_formula"

definition q208416_at_most_formula :: q208416_formula where
  "q208416_at_most_formula =
    q208416_ex (q208416_ex
      (q208416_and
        (q208416_and
          (q208416_subset
            (Q208416_Var 1) (Q208416_Var 3))
          q208416_is_reversed_function_formula)
        (Q208416_All
          (Q208416_Imp
            (Q208416_Mem (Q208416_Var 0) (Q208416_Var 3))
            (q208416_ex
              (q208416_and
                (Q208416_Mem
                  (Q208416_Var 0) (Q208416_Var 3))
                (Q208416_Mem
                  (Q208416_Pair
                    (Q208416_Var 0) (Q208416_Var 1))
                  (Q208416_Var 2))))))))"

definition q208416_CH :: q208416_formula where
  "q208416_CH =
    Q208416_All
      (Q208416_Imp
        q208416_ordinal_formula
        (q208416_or
          (q208416_subst_formula
            q208416_at_most_formula Q208416_Omega 1)
          (q208416_subst_formula
            q208416_at_most_formula
            (Q208416_Powerset Q208416_Omega) 0)))"

inductive q208416_prf ::
    "q208416_formula set \<Rightarrow> q208416_formula \<Rightarrow> bool" where
  axm:
    "A \<in> Gamma \<Longrightarrow> q208416_prf Gamma A"
| impI:
    "q208416_prf (insert A Gamma) B \<Longrightarrow>
      q208416_prf Gamma (Q208416_Imp A B)"
| impE:
    "\<lbrakk>q208416_prf Gamma (Q208416_Imp A B);
      q208416_prf Gamma A\<rbrakk> \<Longrightarrow>
      q208416_prf Gamma B"
| falsumE:
    "q208416_prf (insert (q208416_not A) Gamma) Q208416_False \<Longrightarrow>
      q208416_prf Gamma A"
| allI:
    "q208416_prf
      ((\<lambda>A. q208416_lift_formula_at A 1 0) ` Gamma) A \<Longrightarrow>
      q208416_prf Gamma (Q208416_All A)"
| allE:
    "q208416_prf Gamma (Q208416_All A) \<Longrightarrow>
      q208416_prf Gamma (q208416_subst_formula A t 0)"
| refl:
    "q208416_prf Gamma (Q208416_Eq t t)"
| subst:
    "\<lbrakk>q208416_prf Gamma (Q208416_Eq s t);
      q208416_prf Gamma (q208416_subst_formula A s 0)\<rbrakk> \<Longrightarrow>
      q208416_prf Gamma (q208416_subst_formula A t 0)"

definition q208416_provable ::
    "q208416_formula set \<Rightarrow> q208416_formula \<Rightarrow> bool" where
  "q208416_provable T A \<longleftrightarrow> q208416_prf T A"

definition q208416_independent ::
    "q208416_formula set \<Rightarrow> q208416_formula \<Rightarrow> bool" where
  "q208416_independent T A \<longleftrightarrow>
    (\<not> q208416_provable T A \<and>
     \<not> q208416_provable T (q208416_not A))"

theorem independence_of_CH:
  "q208416_independent q208416_ZFC q208416_CH"
  sorry

end
