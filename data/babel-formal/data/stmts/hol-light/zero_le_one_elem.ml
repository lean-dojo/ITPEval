let one_matrix = new_definition
  `one_matrix (decEq:M->M->bool) (oneA:A) (zeroA:A) =
     (\i j. if decEq i j then oneA else zeroA)`;;

let zero_matrix = new_definition
  `zero_matrix (zeroA:A) = (\i j. zeroA)`;;

let matrix_le = new_definition
  `matrix_le (le:A->A->bool) (A0:M->M->A) (B0:M->M->A) <=>
     !i j. le (A0 i j) (B0 i j)`;;

let matrix_eq = new_definition
  `matrix_eq (A0:M->M->A) (B0:M->M->A) <=> !i j. A0 i j = B0 i j`;;

let zero_le_one_elem =
  `!decEq (zeroA:A) oneA (le:A->A->bool) i j.
      le zeroA oneA ==> le zeroA zeroA ==> le zeroA (one_matrix decEq oneA zeroA i j)`;;

let zero_le_one_matrix =
  `!decEq (zeroA:A) oneA (le:A->A->bool).
      le zeroA oneA ==> le zeroA zeroA ==>
      matrix_le le (zero_matrix zeroA) (one_matrix decEq oneA zeroA)`;;

let matrix_le_refl =
  `!le:A->A->bool. (!x. le x x) ==> !A0:M->M->A. matrix_le le A0 A0`;;

let matrix_le_trans =
  `!le:A->A->bool.
      (!x y z. le x y ==> le y z ==> le x z) ==>
      !A0 B0 C0:M->M->A.
        matrix_le le A0 B0 ==> matrix_le le B0 C0 ==> matrix_le le A0 C0`;;

let matrix_eq_refl =
  `!A0:M->M->A. matrix_eq A0 A0`;;

let matrix_eq_sym =
  `!A0 B0:M->M->A. matrix_eq A0 B0 ==> matrix_eq B0 A0`;;

let matrix_eq_trans =
  `!A0 B0 C0:M->M->A. matrix_eq A0 B0 ==> matrix_eq B0 C0 ==> matrix_eq A0 C0`;;

let matrix_eq_le =
  `!le:A->A->bool.
      (!x. le x x) ==>
      !A0 B0:M->M->A. matrix_eq A0 B0 ==> matrix_le le A0 B0 /\ matrix_le le B0 A0`;;

let matrix_le_antisymm =
  `!le:A->A->bool.
      (!x y. le x y ==> le y x ==> x = y) ==>
      !A0 B0:M->M->A.
        matrix_le le A0 B0 ==> matrix_le le B0 A0 ==> matrix_eq A0 B0`;;
