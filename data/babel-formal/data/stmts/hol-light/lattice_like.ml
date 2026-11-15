let is_lattice_like = new_definition
  `is_lattice_like (le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A) <=>
     (!x. le_rel x x) /\
     (!x y z. le_rel x y /\ le_rel y z ==> le_rel x z) /\
     (!x y. le_rel x y /\ le_rel y x ==> x = y) /\
     (!a b. le_rel (inf_op a b) a) /\
     (!a b. le_rel (inf_op a b) b) /\
     (!c a b. le_rel c a /\ le_rel c b ==> le_rel c (inf_op a b)) /\
     (!a b. le_rel a (sup_op a b)) /\
     (!a b. le_rel b (sup_op a b)) /\
     (!a b c. le_rel a c /\ le_rel b c ==> le_rel (sup_op a b) c)`;;

let INTRO_LATTICE_HYPS =
  REWRITE_TAC[is_lattice_like] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

let inf_comm =
  `!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. inf_op a b = inf_op b a`;;

let sup_comm =
  `!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. sup_op a b = sup_op b a`;;

let inf_assoc =
  `!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==>
      !a b c:A. inf_op (inf_op a b) c = inf_op a (inf_op b c)`;;

let sup_assoc =
  `!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==>
      !a b c:A. sup_op (sup_op a b) c = sup_op a (sup_op b c)`;;

let inf_absorption =
  `!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. inf_op a (sup_op a b) = a`;;

let sup_absorption =
  `!(le_rel:A->A->bool) (inf_op:A->A->A) (sup_op:A->A->A).
      is_lattice_like le_rel inf_op sup_op ==> !a b:A. sup_op a (inf_op a b) = a`;;
