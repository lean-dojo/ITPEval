(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1068085 (thousand-theorems__hol4__Q1068085), "Closed graph theorem": a
  linear map between Banach spaces over a nontrivially normed field is
  continuous when its graph is closed. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory;

val q1068085_nontrivially_normed_field_def = new_definition (
  "q1068085_nontrivially_normed_field_def",
  ``q1068085_nontrivially_normed_field
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real) <=>
      zeroK <> oneK /\
      (!a b. addK a b = addK b a) /\
      (!a b c. addK (addK a b) c = addK a (addK b c)) /\
      (!a. addK a zeroK = a) /\
      (!a. addK a (negK a) = zeroK) /\
      (!a b. mulK a b = mulK b a) /\
      (!a b c. mulK (mulK a b) c = mulK a (mulK b c)) /\
      (!a. mulK a oneK = a) /\
      (!a b c.
        mulK a (addK b c) = addK (mulK a b) (mulK a c)) /\
      invK zeroK = zeroK /\
      (!a. a <> zeroK ==> mulK a (invK a) = oneK) /\
      (!a. 0 <= normK a) /\
      (!a. (normK a = 0) <=> (a = zeroK)) /\
      (!a. normK (negK a) = normK a) /\
      (!a b. normK (addK a b) <= normK a + normK b) /\
      (!a b. normK (mulK a b) = normK a * normK b) /\
      (?a. 1 < normK a)``);

val q1068085_normed_add_comm_group_def = new_definition (
  "q1068085_normed_add_comm_group_def",
  ``q1068085_normed_add_comm_group
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (neg : 'a -> 'a) (norm : 'a -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q1068085_normed_space_def = new_definition (
  "q1068085_normed_space_def",
  ``q1068085_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zero : 'a) (add : 'a -> 'a -> 'a)
      (smul : 'k -> 'a -> 'a) (norm : 'a -> real) <=>
      (!x. smul oneK x = x) /\
      (!a b x. smul (mulK a b) x = smul a (smul b x)) /\
      (!a b x. smul (addK a b) x = add (smul a x) (smul b x)) /\
      (!a x y. smul a (add x y) = add (smul a x) (smul a y)) /\
      (!x. smul zeroK x = zero) /\
      (!a. smul a zero = zero) /\
      (!a x. norm (smul a x) <= normK a * norm x)``);

val q1068085_linear_map_def = new_definition (
  "q1068085_linear_map_def",
  ``q1068085_linear_map
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (addF : 'f -> 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (g : 'e -> 'f) <=>
      (!x y. g (addE x y) = addF (g x) (g y)) /\
      (!a x. g (smulE a x) = smulF a (g x))``);

val q1068085_tendsto_def = new_definition (
  "q1068085_tendsto_def",
  ``q1068085_tendsto
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) (x : 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q1068085_cauchy_def = new_definition (
  "q1068085_cauchy_def",
  ``q1068085_cauchy
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (u : num -> 'a) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q1068085_complete_space_def = new_definition (
  "q1068085_complete_space_def",
  ``q1068085_complete_space
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) <=>
      !u : num -> 'a.
        q1068085_cauchy add neg norm u ==>
        ?x : 'a. q1068085_tendsto add neg norm u x``);

val q1068085_is_closed_graph_def = new_definition (
  "q1068085_is_closed_graph_def",
  ``q1068085_is_closed_graph
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (normF : 'f -> real) (g : 'e -> 'f) <=>
      !u : num -> 'e. !x : 'e. !y : 'f.
        q1068085_tendsto addE negE normE u x /\
        q1068085_tendsto addF negF normF (\n. g (u n)) y
        ==>
        y = g x``);

val q1068085_continuous_def = new_definition (
  "q1068085_continuous_def",
  ``q1068085_continuous
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (normF : 'f -> real) (g : 'e -> 'f) <=>
      !x : 'e. !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !y : 'e.
            normE (addE y (negE x)) < delta ==>
            normF (addF (g y) (negF (g x))) < epsilon``);

val LinearMap_continuous_of_isClosed_graph =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real) (g : 'e -> 'f).
      q1068085_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q1068085_normed_add_comm_group zeroE addE negE normE /\
      q1068085_normed_space
        zeroK oneK addK mulK normK zeroE addE smulE normE /\
      q1068085_complete_space addE negE normE /\
      q1068085_normed_add_comm_group zeroF addF negF normF /\
      q1068085_normed_space
        zeroK oneK addK mulK normK zeroF addF smulF normF /\
      q1068085_complete_space addF negF normF /\
      q1068085_linear_map addE smulE addF smulF g /\
      q1068085_is_closed_graph addE negE normE addF negF normF g
      ==>
      q1068085_continuous addE negE normE addF negF normF g``;
