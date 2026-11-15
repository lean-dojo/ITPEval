(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q3527205, "Dimension theorem for vector spaces": over a semiring with
  invariant basis number, any two bases of the same module have equipotent
  index carriers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open listTheory pred_setTheory;

val q3527205_semiring_def = new_definition (
  "q3527205_semiring_def",
  ``q3527205_semiring
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r) <=>
      (!a b. addR a b = addR b a) /\
      (!a b c. addR (addR a b) c = addR a (addR b c)) /\
      (!a. addR zeroR a = a) /\
      (!a b c. mulR (mulR a b) c = mulR a (mulR b c)) /\
      (!a. mulR oneR a = a) /\
      (!a. mulR a oneR = a) /\
      (!a b c. mulR a (addR b c) = addR (mulR a b) (mulR a c)) /\
      (!a b c. mulR (addR a b) c = addR (mulR a c) (mulR b c)) /\
      (!a. mulR zeroR a = zeroR) /\
      (!a. mulR a zeroR = zeroR)``);

val q3527205_module_def = new_definition (
  "q3527205_module_def",
  ``q3527205_module
      (zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm) <=>
      (!x y. addM x y = addM y x) /\
      (!x y z. addM (addM x y) z = addM x (addM y z)) /\
      (!x. addM zeroM x = x) /\
      (!a x y. smul a (addM x y) = addM (smul a x) (smul a y)) /\
      (!a b x. smul (addR a b) x = addM (smul a x) (smul b x)) /\
      (!a b x. smul (mulR a b) x = smul a (smul b x)) /\
      (!x. smul oneR x = x) /\
      (!x. smul zeroR x = zeroM) /\
      (!a. smul a zeroM = zeroM)``);

val q3527205_lincomb_def = new_definition (
  "q3527205_lincomb_def",
  ``q3527205_lincomb
      (zeroR : 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm)
      (basis : 'i -> 'm) (coeff : 'i -> 'r) =
      ITSET
        (\i acc. addM (smul (coeff i) (basis i)) acc)
        {i | coeff i <> zeroR}
        zeroM``);

val q3527205_basis_def = new_definition (
  "q3527205_basis_def",
  ``q3527205_basis
      (zeroR : 'r) (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm)
      (basis : 'i -> 'm) <=>
      (!coeff coeff' : 'i -> 'r.
        FINITE {i | coeff i <> zeroR} /\
        FINITE {i | coeff' i <> zeroR} /\
        q3527205_lincomb zeroR zeroM addM smul basis coeff =
          q3527205_lincomb zeroR zeroM addM smul basis coeff'
        ==>
        coeff = coeff') /\
      (!x : 'm.
        ?coeff : 'i -> 'r.
          FINITE {i | coeff i <> zeroR} /\
          q3527205_lincomb zeroR zeroM addM smul basis coeff = x)``);

val q3527205_fin_linear_equiv_def = new_definition (
  "q3527205_fin_linear_equiv_def",
  ``q3527205_fin_linear_equiv
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (mulR : 'r -> 'r -> 'r) (n : num) (m : num)
      (f : 'r list -> 'r list) (g : 'r list -> 'r list) <=>
      (!xs. LENGTH xs = n ==> LENGTH (f xs) = m) /\
      (!ys. LENGTH ys = m ==> LENGTH (g ys) = n) /\
      f (REPLICATE n zeroR) = REPLICATE m zeroR /\
      (!xs ys.
        LENGTH xs = n /\ LENGTH ys = n
        ==>
        f (MAP2 addR xs ys) = MAP2 addR (f xs) (f ys)) /\
      (!a xs.
        LENGTH xs = n
        ==>
        f (MAP (mulR a) xs) = MAP (mulR a) (f xs)) /\
      (!xs. LENGTH xs = n ==> g (f xs) = xs) /\
      (!ys. LENGTH ys = m ==> f (g ys) = ys)``);

val q3527205_invariant_basis_number_def = new_definition (
  "q3527205_invariant_basis_number_def",
  ``q3527205_invariant_basis_number
      (zeroR : 'r) (addR : 'r -> 'r -> 'r)
      (mulR : 'r -> 'r -> 'r) <=>
      !n m f g.
        q3527205_fin_linear_equiv zeroR addR mulR n m f g
        ==>
        n = m``);

val mk_eq_mk_of_basis =
  ``!(zeroR : 'r) (oneR : 'r)
      (addR : 'r -> 'r -> 'r) (mulR : 'r -> 'r -> 'r)
      (zeroM : 'm) (addM : 'm -> 'm -> 'm)
      (smul : 'r -> 'm -> 'm)
      (basis_i : 'i -> 'm) (basis_j : 'j -> 'm).
      q3527205_semiring zeroR oneR addR mulR /\
      q3527205_module zeroR oneR addR mulR zeroM addM smul /\
      q3527205_invariant_basis_number zeroR addR mulR /\
      q3527205_basis zeroR zeroM addM smul basis_i /\
      q3527205_basis zeroR zeroM addM smul basis_j
      ==>
      ?e : 'i -> 'j. BIJ e UNIV UNIV``;
