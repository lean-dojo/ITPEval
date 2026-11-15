(*
  Statement-only formalization of the VERINA artifact verina_basic_90
  (SlopeSearch): a fuel-bounded staircase search over a rectangular integer
  matrix with sorted rows and columns returns either a matching coordinate or
  (-1,-1) when the key is absent. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory;

val SlopeSearch_toNat_def = new_definition (
  "SlopeSearch_toNat_def",
  ``SlopeSearch_toNat (i:int) = if i < 0 then 0 else Num i``);

val SlopeSearch_rowBang_def = new_definition (
  "SlopeSearch_rowBang_def",
  ``SlopeSearch_rowBang (a:int list list) i =
      if i < LENGTH a then EL i a else []``);

val SlopeSearch_getBang_def = new_definition (
  "SlopeSearch_getBang_def",
  ``SlopeSearch_getBang (xs:int list) i =
      if i < LENGTH xs then EL i xs else 0``);

val get2d_def = new_definition (
  "get2d_def",
  ``get2d (a:int list list) (i:int) (j:int) =
      SlopeSearch_getBang
        (SlopeSearch_rowBang a (SlopeSearch_toNat i))
        (SlopeSearch_toNat j)``);

val SlopeSearch_pairwiseSameLength_def = Define `
  (SlopeSearch_pairwiseSameLength ([]:int list list) = T) /\
  (SlopeSearch_pairwiseSameLength (x::xs) =
     (EVERY (\y:int list. LENGTH x = LENGTH y) xs /\
      SlopeSearch_pairwiseSameLength xs))`;

val SlopeSearch_pairwiseLe_def = Define `
  (SlopeSearch_pairwiseLe ([]:int list) = T) /\
  (SlopeSearch_pairwiseLe (x::xs) =
     (EVERY (\y:int. x <= y) xs /\
      SlopeSearch_pairwiseLe xs))`;

val SlopeSearch_precond_def = new_definition (
  "SlopeSearch_precond_def",
  ``SlopeSearch_precond (a:int list list) (key:int) <=>
      0 < LENGTH a /\
      0 < LENGTH (SlopeSearch_rowBang a 0) /\
      SlopeSearch_pairwiseSameLength a /\
      EVERY SlopeSearch_pairwiseLe a /\
      EVERY
        (\i. SlopeSearch_pairwiseLe
               (MAP (\row. SlopeSearch_getBang row i) a))
        (COUNT_LIST (LENGTH (SlopeSearch_rowBang a 0)))``);

val SlopeSearch_auxFuel_def = Define `
  (SlopeSearch_auxFuel (a:int list list) (key:int) rows 0
     (m:int) (n:int) = ((-1:int),(-1:int))) /\
  (SlopeSearch_auxFuel a key rows (SUC fuel) m n =
     if int_of_num rows <= m \/ n < 0 then
       ((-1:int),(-1:int))
     else if get2d a m n = key then
       (m,n)
     else if get2d a m n < key then
       SlopeSearch_auxFuel a key rows fuel (m + 1) n
     else
       SlopeSearch_auxFuel a key rows fuel m (n - 1))`;

val SlopeSearch_def = new_definition (
  "SlopeSearch_def",
  ``SlopeSearch (a:int list list) (key:int) =
      let rows = LENGTH a in
      let cols =
        if 0 < rows then LENGTH (SlopeSearch_rowBang a 0) else 0
      in
        SlopeSearch_auxFuel a key rows (rows + cols)
          0 (int_of_num (cols - 1))``);

val SlopeSearch_postcond_def = new_definition (
  "SlopeSearch_postcond_def",
  ``SlopeSearch_postcond (a:int list list) (key:int)
       (result:int # int) <=>
      let m = FST result in
      let n = SND result in
        (0 <= m /\
         m < int_of_num (LENGTH a) /\
         0 <= n /\
         n < int_of_num (LENGTH (SlopeSearch_rowBang a 0)) /\
         get2d a m n = key) \/
        (m = -1 /\ n = -1 /\
         EVERY (\row. EVERY (\entry. entry <> key) row) a)``);

val SlopeSearch_correct_statement = ``
  !a key.
    SlopeSearch_precond a key ==>
    SlopeSearch_postcond a key (SlopeSearch a key)
``;
