(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q25378690, "Ionescu-Tulcea theorem": a sequence of Markov kernels on
  successive measurable state spaces determines a Markov kernel on infinite
  trajectories with the recursively specified finite marginals. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory extrealTheory;
open sigma_algebraTheory measureTheory borelTheory lebesgueTheory;
open probabilityTheory;

val q25378690_history_carrier_def = new_definition (
  "q25378690_history_carrier_def",
  ``q25378690_history_carrier
      (spaces : num -> 'x algebra) (n : num) =
      {h : (num -> 'x) | !i. i <= n ==> h i IN space (spaces i)}``);

val q25378690_path_carrier_def = new_definition (
  "q25378690_path_carrier_def",
  ``q25378690_path_carrier (spaces : num -> 'x algebra) =
      {x : (num -> 'x) | !i. x i IN space (spaces i)}``);

val q25378690_history_space_def = new_definition (
  "q25378690_history_space_def",
  ``q25378690_history_space
      (spaces : num -> 'x algebra) (n : num) =
      sigma
        (q25378690_history_carrier spaces n)
        {c : (num -> 'x) set |
          ?i s.
            i <= n /\
            s IN subsets (spaces i) /\
            c =
              {h |
                h IN q25378690_history_carrier spaces n /\
                h i IN s}}``);

val q25378690_path_space_def = new_definition (
  "q25378690_path_space_def",
  ``q25378690_path_space (spaces : num -> 'x algebra) =
      sigma
        (q25378690_path_carrier spaces)
        {c : (num -> 'x) set |
          ?i s.
            s IN subsets (spaces i) /\
            c =
              {x |
                x IN q25378690_path_carrier spaces /\
                x i IN s}}``);

val q25378690_same_history_def = new_definition (
  "q25378690_same_history_def",
  ``q25378690_same_history (n : num)
      (h : num -> 'x) (h' : num -> 'x) <=>
      !i. i <= n ==> h i = h' i``);

val q25378690_update_def = new_definition (
  "q25378690_update_def",
  ``q25378690_update (h : num -> 'x) (n : num) (y : 'x) =
      \i. if i = n then y else h i``);

val q25378690_markov_kernel_def = new_definition (
  "q25378690_markov_kernel_def",
  ``q25378690_markov_kernel
      (source : 'a algebra) (target : 'b algebra)
      (k : 'a -> 'b m_space) <=>
      sigma_algebra source /\
      sigma_algebra target /\
      (!x.
        x IN space source ==>
        prob_space (k x) /\
        m_space (k x) = space target /\
        measurable_sets (k x) = subsets target) /\
      (!s.
        s IN subsets target ==>
        (\x. measure (k x) s) IN measurable source Borel)``);

val q25378690_history_extensional_def = new_definition (
  "q25378690_history_extensional_def",
  ``q25378690_history_extensional
      (spaces : num -> 'x algebra) (n : num)
      (k : (num -> 'x) -> 'y) <=>
      !h h'.
        h IN q25378690_history_carrier spaces n /\
        h' IN q25378690_history_carrier spaces n /\
        q25378690_same_history n h h'
        ==>
        k h = k h'``);

val q25378690_finite_family_def = new_definition (
  "q25378690_finite_family_def",
  ``q25378690_finite_family
      (spaces : num -> 'x algebra)
      (kappa : num -> (num -> 'x) -> 'x m_space)
      (a : num) (x : num -> 'x)
      (mu : num -> (num -> 'x) m_space) <=>
      (!b.
        prob_space (mu b) /\
        m_space (mu b) =
          q25378690_history_carrier spaces b /\
        measurable_sets (mu b) =
          subsets (q25378690_history_space spaces b)) /\
      (!b s.
        b <= a /\
        s IN subsets (q25378690_history_space spaces b)
        ==>
        measure (mu b) s =
          if x IN s then 1 else 0) /\
      (!b s.
        a <= b /\
        s IN subsets (q25378690_history_space spaces (b + 1))
        ==>
        measure (mu (b + 1)) s =
          pos_fn_integral
            (mu b)
            (\h.
              measure
                (kappa b h)
                {y |
                  y IN space (spaces (b + 1)) /\
                  q25378690_update h (b + 1) y IN s}))``);

val q25378690_traj_witness_def = new_definition (
  "q25378690_traj_witness_def",
  ``q25378690_traj_witness
      (spaces : num -> 'x algebra)
      (kappa : num -> (num -> 'x) -> 'x m_space)
      (traj : num -> (num -> 'x) -> (num -> 'x) m_space) <=>
      !a.
        q25378690_markov_kernel
          (q25378690_history_space spaces a)
          (q25378690_path_space spaces)
          (traj a) /\
        q25378690_history_extensional spaces a (traj a) /\
        !x.
          x IN q25378690_history_carrier spaces a ==>
          ?mu : num -> (num -> 'x) m_space.
            q25378690_finite_family spaces kappa a x mu /\
            !b s.
              s IN subsets (q25378690_history_space spaces b)
              ==>
              distr (traj a x) I s = measure (mu b) s``);

val ionescu_tulcea_theorem =
  ``!(spaces : num -> 'x algebra)
      (kappa : num -> (num -> 'x) -> 'x m_space).
      (!n. sigma_algebra (spaces n)) /\
      (!n.
        q25378690_markov_kernel
          (q25378690_history_space spaces n)
          (spaces (n + 1))
          (kappa n)) /\
      (!n.
        q25378690_history_extensional spaces n (kappa n))
      ==>
      ?traj : num -> (num -> 'x) -> (num -> 'x) m_space.
        q25378690_traj_witness spaces kappa traj``;
