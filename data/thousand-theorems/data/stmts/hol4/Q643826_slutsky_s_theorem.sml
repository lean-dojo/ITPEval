(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q643826 (thousand-theorems__hol4__Q643826), "Slutsky's theorem": convergence
  in distribution of one random variable and convergence in probability of
  another to a constant are preserved after pairing and applying a continuous
  function. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory pred_setTheory realTheory extrealTheory;
open topologyTheory real_topologyTheory sigma_algebraTheory measureTheory;
open borelTheory lebesgueTheory probabilityTheory;

val q643826_filter_def = new_definition (
  "q643826_filter_def",
  ``q643826_filter (L : ('i set) set) <=>
      UNIV IN L /\
      (!s t. s IN L /\ s SUBSET t ==> t IN L) /\
      (!s t. s IN L /\ t IN L ==> s INTER t IN L)``);

val q643826_countably_generated_def = new_definition (
  "q643826_countably_generated_def",
  ``q643826_countably_generated (L : ('i set) set) <=>
      ?B : num -> 'i set.
        (!m n. m <= n ==> B n SUBSET B m) /\
        !s. s IN L <=> ?n. B n SUBSET s``);

val q643826_seminormed_add_comm_group_def = new_definition (
  "q643826_seminormed_add_comm_group_def",
  ``q643826_seminormed_add_comm_group
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (norm : 'e -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x. 0 <= norm x) /\
      norm zero = 0 /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q643826_norm_topology_def = new_definition (
  "q643826_norm_topology_def",
  ``q643826_norm_topology
      (top : 'e topology)
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      topspace top = UNIV /\
      !u. open_in top u <=>
        !x. x IN u ==>
          ?epsilon : real.
            0 < epsilon /\
            !y. norm (add y (neg x)) < epsilon ==> y IN u``);

val q643826_second_countable_def = new_definition (
  "q643826_second_countable_def",
  ``q643826_second_countable (top : 'e topology) <=>
      ?basis : ('e set) set.
        COUNTABLE basis /\
        (!v. v IN basis ==> open_in top v) /\
        !u x.
          open_in top u /\ x IN u ==>
          ?v. v IN basis /\ x IN v /\ v SUBSET u``);

val q643826_borel_space_def = new_definition (
  "q643826_borel_space_def",
  ``q643826_borel_space
      (top : 'e topology) (a : 'e algebra) <=>
      topspace top = UNIV /\
      a = general_borel top``);

val q643826_pair_continuous_def = new_definition (
  "q643826_pair_continuous_def",
  ``q643826_pair_continuous
      (topE : 'e topology) (topD : 'd topology)
      (topF : 'f topology) (g : 'e # 'd -> 'f) <=>
      !v. open_in topF v ==>
        !p. g p IN v ==>
          ?u w.
            open_in topE u /\
            open_in topD w /\
            FST p IN u /\
            SND p IN w /\
            !q. FST q IN u /\ SND q IN w ==> g q IN v``);

val q643826_ae_measurable_def = new_definition (
  "q643826_ae_measurable_def",
  ``q643826_ae_measurable
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) <=>
      ?h.
        h IN measurable (m_space m,measurable_sets m) a /\
        almost_everywhere m (\x. f x = h x)``);

val q643826_measurable_rep_def = new_definition (
  "q643826_measurable_rep_def",
  ``q643826_measurable_rep
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) =
      @h.
        h IN measurable (m_space m,measurable_sets m) a /\
        almost_everywhere m (\x. f x = h x)``);

val q643826_law_def = new_definition (
  "q643826_law_def",
  ``q643826_law
      (m : 'a m_space) (a : 'b algebra) (f : 'a -> 'b) =
      (space a,subsets a,distr m (q643826_measurable_rep m a f))``);

val q643826_weak_tendsto_def = new_definition (
  "q643826_weak_tendsto_def",
  ``q643826_weak_tendsto
      (top : 'a topology) (L : ('i set) set)
      (nu : 'i -> 'a m_space) (nu0 : 'a m_space) <=>
      !f.
        f IN bounded_continuous top ==>
        !epsilon : real.
          0 < epsilon ==>
          {i |
            dist extreal_mr1
              (integral (nu i) (Normal o f),
               integral nu0 (Normal o f)) < epsilon} IN L``);

val q643826_tendsto_in_distribution_def = new_definition (
  "q643826_tendsto_in_distribution_def",
  ``q643826_tendsto_in_distribution
      (top : 'e topology) (a : 'e algebra) (L : ('i set) set)
      (mu : 'i -> 'w m_space) (mu0 : 'w0 m_space)
      (X : 'i -> 'w -> 'e) (Z : 'w0 -> 'e) <=>
      (!i. q643826_ae_measurable (mu i) a (X i)) /\
      q643826_ae_measurable mu0 a Z /\
      q643826_weak_tendsto top L
        (\i. q643826_law (mu i) a (X i))
        (q643826_law mu0 a Z)``);

val q643826_outer_measure_def = new_definition (
  "q643826_outer_measure_def",
  ``q643826_outer_measure (m : 'a m_space) (s : 'a set) =
      inf
        {r : extreal |
          ?t : 'a set.
            s SUBSET t /\
            t IN measurable_sets m /\
            measure m t = r}``);

val q643826_tendsto_extreal_def = new_definition (
  "q643826_tendsto_extreal_def",
  ``q643826_tendsto_extreal
      (L : ('i set) set) (u : 'i -> extreal) (ell : extreal) <=>
      !epsilon : real.
        0 < epsilon ==>
        {i | dist extreal_mr1 (u i,ell) < epsilon} IN L``);

val q643826_tendsto_in_measure_def = new_definition (
  "q643826_tendsto_in_measure_def",
  ``q643826_tendsto_in_measure
      (m : 'a m_space) (L : ('i set) set)
      (add : 'd -> 'd -> 'd) (neg : 'd -> 'd)
      (norm : 'd -> real)
      (Y : 'i -> 'a -> 'd) (c : 'd) <=>
      !epsilon : real.
        0 < epsilon ==>
        q643826_tendsto_extreal L
          (\i.
            q643826_outer_measure m
              {x | epsilon <= norm (add (Y i x) (neg c))})
          0``);

val slutsky_s_theorem =
  ``!(topE : 'e topology) (measE : 'e algebra)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (normE : 'e -> real)
      (topD : 'd topology) (measD : 'd algebra)
      (zeroD : 'd) (addD : 'd -> 'd -> 'd)
      (negD : 'd -> 'd) (normD : 'd -> real)
      (topF : 'f topology) (measF : 'f algebra)
      (L : ('i set) set)
      (mu : 'w m_space) (mu0 : 'w0 m_space)
      (X : 'i -> 'w -> 'e) (Y : 'i -> 'w -> 'd)
      (Z : 'w0 -> 'e) (c : 'd) (g : 'e # 'd -> 'f).
      q643826_filter L /\
      q643826_countably_generated L /\
      prob_space mu /\
      m_space mu = UNIV /\
      prob_space mu0 /\
      m_space mu0 = UNIV /\
      q643826_seminormed_add_comm_group zeroE addE negE normE /\
      q643826_norm_topology topE addE negE normE /\
      q643826_second_countable topE /\
      q643826_borel_space topE measE /\
      q643826_seminormed_add_comm_group zeroD addD negD normD /\
      q643826_norm_topology topD addD negD normD /\
      q643826_second_countable topD /\
      q643826_borel_space topD measD /\
      topspace topF = UNIV /\
      q643826_borel_space topF measF /\
      q643826_pair_continuous topE topD topF g /\
      q643826_tendsto_in_distribution
        topE measE L (\i. mu) mu0 X Z /\
      q643826_tendsto_in_measure mu L addD negD normD Y c /\
      (!i. q643826_ae_measurable mu measD (Y i))
      ==>
      q643826_tendsto_in_distribution
        topF measF L (\i. mu) mu0
        (\i w. g (X i w,Y i w))
        (\w. g (Z w,c))``;
