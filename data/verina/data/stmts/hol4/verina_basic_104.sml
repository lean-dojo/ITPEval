(*
  Statement-only formalization of VERINA corpus artifact verina_basic_104,
  catalog title "update_map": the executable association-list map update
  gives second-map entries precedence, retains unoverridden first-map entries,
  and sorts the result by integer key. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory optionTheory pairTheory;

val update_map_precond_def = new_definition (
  "update_map_precond_def",
  ``update_map_precond
      (m1 : (int # int) list) (m2 : (int # int) list) <=>
      ALL_DISTINCT (MAP FST m1) /\
      ALL_DISTINCT (MAP FST m2)``
);

val update_map_insert_def = new_definition (
  "update_map_insert_def",
  ``update_map_insert
      (m : (int # int) list) (k : int) (v : int) =
      FILTER (\entry. FST entry <> k) m ++ [(k,v)]``
);

val update_map_sort_insert_def = Define `
  (update_map_sort_insert
      (entry : int # int) ([] : (int # int) list) =
     [entry]) /\
  (update_map_sort_insert
      entry (head::tail) =
     if FST entry <= FST head then
       entry::head::tail
     else
       head::update_map_sort_insert entry tail)
`;

val update_map_sort_def = Define `
  (update_map_sort
      ([] : (int # int) list) =
     ([] : (int # int) list)) /\
  (update_map_sort
      (entry::rest) =
     update_map_sort_insert entry (update_map_sort rest))
`;

val update_map_def = new_definition (
  "update_map_def",
  ``update_map
      (m1 : (int # int) list) (m2 : (int # int) list) =
      let updated =
        FOLDL
          (\acc entry.
             update_map_insert acc (FST entry) (SND entry))
          m1
          m2
      in
        update_map_sort updated``
);

val update_map_find_def = Define `
  (update_map_find
      ([] : (int # int) list) (k : int) =
     (NONE : int option)) /\
  (update_map_find
      ((key,value)::rest) k =
     if key = k then
       SOME value
     else
       update_map_find rest k)
`;

val update_map_pairwise_def = Define `
  (update_map_pairwise
      ([] : (int # int) list) =
     T) /\
  (update_map_pairwise
      (entry::rest) =
     (EVERY
        (\later : int # int. FST entry <= FST later)
        rest /\
      update_map_pairwise rest))
`;

val update_map_postcond_def = new_definition (
  "update_map_postcond_def",
  ``update_map_postcond
      (m1 : (int # int) list)
      (m2 : (int # int) list)
      (result : (int # int) list) <=>
      update_map_pairwise result /\
      EVERY
        (\entry.
           update_map_find result (FST entry) =
           SOME (SND entry))
        m2 /\
      EVERY
        (\entry.
           case update_map_find m2 (FST entry) of
             NONE =>
               update_map_find result (FST entry) =
               SOME (SND entry)
           | SOME value => T)
        m1 /\
      EVERY
        (\entry.
           case update_map_find m1 (FST entry) of
             NONE =>
               update_map_find m2 (FST entry) =
               SOME (SND entry)
           | SOME value =>
               (case update_map_find m2 (FST entry) of
                  NONE => SND entry = value
                | SOME value2 => SND entry = value2))
        result``
);

val update_map_spec_satisfied =
  ``!(m1 : (int # int) list) (m2 : (int # int) list).
      update_map_precond m1 m2 ==>
      update_map_postcond m1 m2 (update_map m1 m2)``;
