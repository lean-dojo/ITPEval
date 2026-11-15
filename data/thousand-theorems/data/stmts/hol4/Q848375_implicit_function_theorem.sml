(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q848375 (thousand-theorems__hol4__Q848375), "Implicit function theorem":
  for general Banach-space implicit-function data, the implicit function is
  the curried inverse of the specifically derived local open partial
  homeomorphism. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory realTheory;

val q848375_nontrivially_normed_field_def = new_definition (
  "q848375_nontrivially_normed_field_def",
  ``q848375_nontrivially_normed_field
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

val q848375_normed_add_comm_group_def = new_definition (
  "q848375_normed_add_comm_group_def",
  ``q848375_normed_add_comm_group
      (zero : 'e) (add : 'e -> 'e -> 'e)
      (neg : 'e -> 'e) (norm : 'e -> real) <=>
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z)) /\
      (!x. add x zero = x) /\
      (!x. add x (neg x) = zero) /\
      norm zero = 0 /\
      (!x. 0 <= norm x) /\
      (!x. (norm x = 0) <=> (x = zero)) /\
      (!x. norm (neg x) = norm x) /\
      (!x y. norm (add x y) <= norm x + norm y)``);

val q848375_normed_space_def = new_definition (
  "q848375_normed_space_def",
  ``q848375_normed_space
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real) <=>
      (!x. smulE oneK x = x) /\
      (!a b x. smulE (mulK a b) x = smulE a (smulE b x)) /\
      (!a b x. smulE (addK a b) x = addE (smulE a x) (smulE b x)) /\
      (!a x y. smulE a (addE x y) = addE (smulE a x) (smulE a y)) /\
      (!x. smulE zeroK x = zeroE) /\
      (!a. smulE a zeroE = zeroE) /\
      (!a x. normE (smulE a x) = normK a * normE x)``);

val q848375_tendsto_def = new_definition (
  "q848375_tendsto_def",
  ``q848375_tendsto
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) (x : 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !n : num.
          N <= n ==> norm (add (u n) (neg x)) < epsilon``);

val q848375_cauchy_def = new_definition (
  "q848375_cauchy_def",
  ``q848375_cauchy
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) (u : num -> 'e) <=>
      !epsilon : real.
        0 < epsilon ==>
        ?N : num. !m n : num.
          N <= m /\ N <= n ==>
          norm (add (u m) (neg (u n))) < epsilon``);

val q848375_complete_space_def = new_definition (
  "q848375_complete_space_def",
  ``q848375_complete_space
      (add : 'e -> 'e -> 'e) (neg : 'e -> 'e)
      (norm : 'e -> real) <=>
      !u : num -> 'e.
        q848375_cauchy add neg norm u ==>
        ?x : 'e. q848375_tendsto add neg norm u x``);

val q848375_continuous_linear_map_def = new_definition (
  "q848375_continuous_linear_map_def",
  ``q848375_continuous_linear_map
      (addE : 'e -> 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real) (L : 'e -> 'f) <=>
      (!x y. L (addE x y) = addF (L x) (L y)) /\
      (!a x. L (smulE a x) = smulF a (L x)) /\
      ?C : real.
        0 <= C /\
        !x. normF (L x) <= C * normE x``);

val q848375_has_strict_fderiv_at_def = new_definition (
  "q848375_has_strict_fderiv_at_def",
  ``q848375_has_strict_fderiv_at
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (f : 'e -> 'f) (f' : 'e -> 'f) (a : 'e) <=>
      q848375_continuous_linear_map
        addE smulE normE addF smulF normF f' /\
      !epsilon : real.
        0 < epsilon ==>
        ?delta : real.
          0 < delta /\
          !x y : 'e.
            normE (addE x (negE a)) < delta /\
            normE (addE y (negE a)) < delta
            ==>
            normF
              (addF
                (addF (f x) (negF (f y)))
                (negF (f' (addE x (negE y))))) <=
            epsilon * normE (addE x (negE y))``);

val q848375_surjective_def = new_definition (
  "q848375_surjective_def",
  ``q848375_surjective (f : 'a -> 'b) <=>
      !y : 'b. ?x : 'a. f x = y``);

val q848375_complementary_kernels_def = new_definition (
  "q848375_complementary_kernels_def",
  ``q848375_complementary_kernels
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (zeroF : 'f) (zeroG : 'g)
      (leftDeriv : 'e -> 'f) (rightDeriv : 'e -> 'g) <=>
      (!x.
        leftDeriv x = zeroF /\ rightDeriv x = zeroG ==>
        x = zeroE) /\
      (!x.
        ?u v.
          leftDeriv u = zeroF /\
          rightDeriv v = zeroG /\
          addE u v = x)``);

val q848375_implicit_function_data_def = new_definition (
  "q848375_implicit_function_data_def",
  ``q848375_implicit_function_data
      (zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real)
      (zeroG : 'g) (addG : 'g -> 'g -> 'g)
      (negG : 'g -> 'g) (smulG : 'k -> 'g -> 'g)
      (normG : 'g -> real)
      (leftFun : 'e -> 'f) (leftDeriv : 'e -> 'f)
      (rightFun : 'e -> 'g) (rightDeriv : 'e -> 'g)
      (pt : 'e) <=>
      q848375_nontrivially_normed_field
        zeroK oneK addK mulK negK invK normK /\
      q848375_normed_add_comm_group zeroE addE negE normE /\
      q848375_normed_space
        zeroK oneK addK mulK normK zeroE addE smulE normE /\
      q848375_complete_space addE negE normE /\
      q848375_normed_add_comm_group zeroF addF negF normF /\
      q848375_normed_space
        zeroK oneK addK mulK normK zeroF addF smulF normF /\
      q848375_complete_space addF negF normF /\
      q848375_normed_add_comm_group zeroG addG negG normG /\
      q848375_normed_space
        zeroK oneK addK mulK normK zeroG addG smulG normG /\
      q848375_complete_space addG negG normG /\
      q848375_has_strict_fderiv_at
        addE negE smulE normE addF negF smulF normF
        leftFun leftDeriv pt /\
      q848375_has_strict_fderiv_at
        addE negE smulE normE addG negG smulG normG
        rightFun rightDeriv pt /\
      q848375_surjective leftDeriv /\
      q848375_surjective rightDeriv /\
      q848375_complementary_kernels
        zeroE addE zeroF zeroG leftDeriv rightDeriv``);

val q848375_prod_add_def = new_definition (
  "q848375_prod_add_def",
  ``q848375_prod_add
      (addF : 'f -> 'f -> 'f) (addG : 'g -> 'g -> 'g)
      (p : 'f # 'g) (q : 'f # 'g) =
      (addF (FST p) (FST q), addG (SND p) (SND q))``);

val q848375_prod_neg_def = new_definition (
  "q848375_prod_neg_def",
  ``q848375_prod_neg
      (negF : 'f -> 'f) (negG : 'g -> 'g)
      (p : 'f # 'g) =
      (negF (FST p), negG (SND p))``);

val q848375_prod_smul_def = new_definition (
  "q848375_prod_smul_def",
  ``q848375_prod_smul
      (smulF : 'k -> 'f -> 'f) (smulG : 'k -> 'g -> 'g)
      (a : 'k) (p : 'f # 'g) =
      (smulF a (FST p), smulG a (SND p))``);

val q848375_prod_norm_def = new_definition (
  "q848375_prod_norm_def",
  ``q848375_prod_norm
      (normF : 'f -> real) (normG : 'g -> real)
      (p : 'f # 'g) =
      max (normF (FST p)) (normG (SND p))``);

val q848375_prod_fun_def = new_definition (
  "q848375_prod_fun_def",
  ``q848375_prod_fun
      (leftFun : 'e -> 'f) (rightFun : 'e -> 'g) (x : 'e) =
      (leftFun x, rightFun x)``);

val q848375_prod_deriv_def = new_definition (
  "q848375_prod_deriv_def",
  ``q848375_prod_deriv
      (leftDeriv : 'e -> 'f) (rightDeriv : 'e -> 'g) (x : 'e) =
      (leftDeriv x, rightDeriv x)``);

val q848375_prod_deriv_inverse_def = new_definition (
  "q848375_prod_deriv_inverse_def",
  ``q848375_prod_deriv_inverse
      (leftDeriv : 'e -> 'f) (rightDeriv : 'e -> 'g)
      (p : 'f # 'g) =
      @x : 'e.
        leftDeriv x = FST p /\ rightDeriv x = SND p``);

val q848375_linear_equiv_def = new_definition (
  "q848375_linear_equiv_def",
  ``q848375_linear_equiv
      (forward : 'a -> 'b) (inverse : 'b -> 'a) <=>
      (!x. inverse (forward x) = x) /\
      (!y. forward (inverse y) = y)``);

val q848375_open_set_def = new_definition (
  "q848375_open_set_def",
  ``q848375_open_set
      (add : 'a -> 'a -> 'a) (neg : 'a -> 'a)
      (norm : 'a -> real) (s : 'a -> bool) <=>
      !x.
        x IN s ==>
        ?radius : real.
          0 < radius /\
          !y.
            norm (add y (neg x)) < radius ==>
            y IN s``);

val q848375_continuous_on_def = new_definition (
  "q848375_continuous_on_def",
  ``q848375_continuous_on
      (addA : 'a -> 'a -> 'a) (negA : 'a -> 'a)
      (normA : 'a -> real)
      (addB : 'b -> 'b -> 'b) (negB : 'b -> 'b)
      (normB : 'b -> real)
      (source : 'a -> bool) (f : 'a -> 'b) <=>
      !x.
        x IN source ==>
        !epsilon : real.
          0 < epsilon ==>
          ?delta : real.
            0 < delta /\
            !y.
              y IN source /\
              normA (addA y (negA x)) < delta
              ==>
              normB (addB (f y) (negB (f x))) < epsilon``);

val q848375_open_partial_homeomorph_def = new_definition (
  "q848375_open_partial_homeomorph_def",
  ``q848375_open_partial_homeomorph
      (addA : 'a -> 'a -> 'a) (negA : 'a -> 'a)
      (normA : 'a -> real)
      (addB : 'b -> 'b -> 'b) (negB : 'b -> 'b)
      (normB : 'b -> real)
      (forward : 'a -> 'b) (pt : 'a)
      (h : ('a -> bool) # (('b -> bool) # ('b -> 'a))) <=>
      let source = FST h in
      let target = FST (SND h) in
      let inverse = SND (SND h) in
        q848375_open_set addA negA normA source /\
        q848375_open_set addB negB normB target /\
        pt IN source /\
        forward pt IN target /\
        (!x.
          x IN source ==>
          forward x IN target /\ inverse (forward x) = x) /\
        (!y.
          y IN target ==>
          inverse y IN source /\ forward (inverse y) = y) /\
        q848375_continuous_on
          addA negA normA addB negB normB source forward /\
        q848375_continuous_on
          addB negB normB addA negA normA target inverse``);

val q848375_has_strict_fderiv_to_open_partial_homeomorph_def =
  new_definition (
    "q848375_has_strict_fderiv_to_open_partial_homeomorph_def",
    ``q848375_has_strict_fderiv_to_open_partial_homeomorph
        (addA : 'a -> 'a -> 'a) (negA : 'a -> 'a)
        (smulA : 'k -> 'a -> 'a) (normA : 'a -> real)
        (addB : 'b -> 'b -> 'b) (negB : 'b -> 'b)
        (smulB : 'k -> 'b -> 'b) (normB : 'b -> real)
        (f : 'a -> 'b) (f' : 'a -> 'b) (f'inv : 'b -> 'a)
        (pt : 'a) =
        @h : ('a -> bool) # (('b -> bool) # ('b -> 'a)).
          q848375_has_strict_fderiv_at
            addA negA smulA normA addB negB smulB normB f f' pt /\
          q848375_linear_equiv f' f'inv /\
          q848375_open_partial_homeomorph
            addA negA normA addB negB normB f pt h``);

val q848375_to_open_partial_homeomorph_def = new_definition (
  "q848375_to_open_partial_homeomorph_def",
  ``q848375_to_open_partial_homeomorph
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (addG : 'g -> 'g -> 'g) (negG : 'g -> 'g)
      (smulG : 'k -> 'g -> 'g) (normG : 'g -> real)
      (leftFun : 'e -> 'f) (leftDeriv : 'e -> 'f)
      (rightFun : 'e -> 'g) (rightDeriv : 'e -> 'g)
      (pt : 'e) =
      q848375_has_strict_fderiv_to_open_partial_homeomorph
        addE negE smulE normE
        (q848375_prod_add addF addG)
        (q848375_prod_neg negF negG)
        (q848375_prod_smul smulF smulG)
        (q848375_prod_norm normF normG)
        (q848375_prod_fun leftFun rightFun)
        (q848375_prod_deriv leftDeriv rightDeriv)
        (q848375_prod_deriv_inverse leftDeriv rightDeriv)
        pt``);

val q848375_implicit_function_def = new_definition (
  "q848375_implicit_function_def",
  ``q848375_implicit_function
      (addE : 'e -> 'e -> 'e) (negE : 'e -> 'e)
      (smulE : 'k -> 'e -> 'e) (normE : 'e -> real)
      (addF : 'f -> 'f -> 'f) (negF : 'f -> 'f)
      (smulF : 'k -> 'f -> 'f) (normF : 'f -> real)
      (addG : 'g -> 'g -> 'g) (negG : 'g -> 'g)
      (smulG : 'k -> 'g -> 'g) (normG : 'g -> real)
      (leftFun : 'e -> 'f) (leftDeriv : 'e -> 'f)
      (rightFun : 'e -> 'g) (rightDeriv : 'e -> 'g)
      (pt : 'e) (x : 'f) (y : 'g) =
      SND
        (SND
          (q848375_to_open_partial_homeomorph
            addE negE smulE normE
            addF negF smulF normF
            addG negG smulG normG
            leftFun leftDeriv rightFun rightDeriv pt))
        (x,y)``);

val ImplicitFunctionData_implicitFunction =
  ``!(zeroK : 'k) (oneK : 'k)
      (addK : 'k -> 'k -> 'k) (mulK : 'k -> 'k -> 'k)
      (negK : 'k -> 'k) (invK : 'k -> 'k)
      (normK : 'k -> real)
      (zeroE : 'e) (addE : 'e -> 'e -> 'e)
      (negE : 'e -> 'e) (smulE : 'k -> 'e -> 'e)
      (normE : 'e -> real)
      (zeroF : 'f) (addF : 'f -> 'f -> 'f)
      (negF : 'f -> 'f) (smulF : 'k -> 'f -> 'f)
      (normF : 'f -> real)
      (zeroG : 'g) (addG : 'g -> 'g -> 'g)
      (negG : 'g -> 'g) (smulG : 'k -> 'g -> 'g)
      (normG : 'g -> real)
      (leftFun : 'e -> 'f) (leftDeriv : 'e -> 'f)
      (rightFun : 'e -> 'g) (rightDeriv : 'e -> 'g)
      (pt : 'e).
      q848375_implicit_function_data
        zeroK oneK addK mulK negK invK normK
        zeroE addE negE smulE normE
        zeroF addF negF smulF normF
        zeroG addG negG smulG normG
        leftFun leftDeriv rightFun rightDeriv pt
      ==>
      (
        q848375_open_partial_homeomorph
          addE negE normE
          (q848375_prod_add addF addG)
          (q848375_prod_neg negF negG)
          (q848375_prod_norm normF normG)
          (q848375_prod_fun leftFun rightFun)
          pt
          (q848375_to_open_partial_homeomorph
            addE negE smulE normE
            addF negF smulF normF
            addG negG smulG normG
            leftFun leftDeriv rightFun rightDeriv pt)
        /\
        !x : 'f. !y : 'g.
          q848375_implicit_function
            addE negE smulE normE
            addF negF smulF normF
            addG negG smulG normG
            leftFun leftDeriv rightFun rightDeriv pt x y =
          SND
            (SND
              (q848375_to_open_partial_homeomorph
                addE negE smulE normE
                addF negF smulF normF
                addG negG smulG normG
                leftFun leftDeriv rightFun rightDeriv pt))
            (x,y)
      )``;
