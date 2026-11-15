(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1259814,
  "Nielsen–Schreier theorem": every subgroup of a free group is itself a free
  group, expressed through unique reduced signed words over a basis. This file
  contains no proof.
*)

loads "Library/grouptheory.ml";;

let Q1259814_NIELSEN_SCHREIER_THEOREM =
  `let reduced_word =
     \(basis:A->bool) (word:(A#bool)list).
       ALL (\letter. FST letter IN basis) word /\
       (!i. i + 1 < LENGTH word
            ==> ~(FST (EL i word) = FST (EL (i + 1) word) /\
                  ~(SND (EL i word) = SND (EL (i + 1) word)))) in
   let word_value =
     \(K:A group) (word:(A#bool)list).
       ITLIST
         (\letter value.
            group_mul K
              (if SND letter
               then FST letter
               else group_inv K (FST letter))
              value)
         word (group_id K) in
   let is_free_group =
     \(K:A group).
       ?basis:A->bool.
         basis SUBSET group_carrier K /\
         (!x. x IN group_carrier K
              ==> ?!word:(A#bool)list.
                    reduced_word basis word /\
                    word_value K word = x) in
   !G:A group. !H:A->bool.
     H subgroup_of G /\ is_free_group G
     ==> is_free_group (subgroup_generated G H)`;;
