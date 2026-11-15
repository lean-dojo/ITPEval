(*
  Statement-only formalization of VERINA corpus artifact verina_basic_104,
  catalog title "update_map": an executable association-list map update folds
  the second integer map into the first with overwrite semantics, sorts the
  result by key, and states the complete map-correctness contract. This file
  contains no proof.
*)

theory verina_basic_104
  imports Main
begin

datatype ('k, 'v) verina_map = Map "('k \<times> 'v) list"

fun map_entries :: "('k, 'v) verina_map \<Rightarrow> ('k \<times> 'v) list" where
  "map_entries (Map entries) = entries"

definition update_map_map_beq ::
    "('k, 'v) verina_map \<Rightarrow> ('k, 'v) verina_map \<Rightarrow> bool" where
  "update_map_map_beq m1 m2 \<longleftrightarrow>
    length (map_entries m1) = length (map_entries m2) \<and>
    map_entries m1 = map_entries m2"

definition update_map_empty :: "('k, 'v) verina_map" where
  "update_map_empty = Map []"

definition update_map_insert ::
    "('k, 'v) verina_map \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow>
      ('k, 'v) verina_map" where
  "update_map_insert m k v =
    Map (filter (\<lambda>p. fst p \<noteq> k) (map_entries m) @ [(k, v)])"

fun update_map_find_entries ::
    "('k \<times> 'v) list \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "update_map_find_entries [] k = None"
| "update_map_find_entries (p # ps) k =
    (if fst p = k
     then Some (snd p)
     else update_map_find_entries ps k)"

definition update_map_find ::
    "('k, 'v) verina_map \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "update_map_find m k =
    update_map_find_entries (map_entries m) k"

definition update_map_precond ::
    "(int, int) verina_map \<Rightarrow> (int, int) verina_map \<Rightarrow> bool"
  where
  "update_map_precond m1 m2 \<longleftrightarrow>
    distinct (map fst (map_entries m1)) \<and>
    distinct (map fst (map_entries m2))"

definition update_map_fold_step ::
    "(int, int) verina_map \<Rightarrow> (int \<times> int) \<Rightarrow>
      (int, int) verina_map" where
  "update_map_fold_step acc entry =
    update_map_insert acc (fst entry) (snd entry)"

fun update_map_sort_insert ::
    "(int \<times> int) \<Rightarrow> (int \<times> int) list \<Rightarrow>
      (int \<times> int) list" where
  "update_map_sort_insert p [] = [p]"
| "update_map_sort_insert p (q # qs) =
    (if fst p \<le> fst q
     then p # q # qs
     else q # update_map_sort_insert p qs)"

fun update_map_sort ::
    "(int \<times> int) list \<Rightarrow> (int \<times> int) list" where
  "update_map_sort [] = []"
| "update_map_sort (p # ps) =
    update_map_sort_insert p (update_map_sort ps)"

definition update_map ::
    "(int, int) verina_map \<Rightarrow> (int, int) verina_map \<Rightarrow>
      (int, int) verina_map" where
  "update_map m1 m2 =
    Map
      (update_map_sort
        (map_entries
          (foldl update_map_fold_step m1 (map_entries m2))))"

fun update_map_pairwise_le ::
    "(int \<times> int) list \<Rightarrow> bool" where
  "update_map_pairwise_le [] = True"
| "update_map_pairwise_le (x # xs) =
    (list_all (\<lambda>y. fst x \<le> fst y) xs \<and>
     update_map_pairwise_le xs)"

definition update_map_postcond ::
    "(int, int) verina_map \<Rightarrow> (int, int) verina_map \<Rightarrow>
      (int, int) verina_map \<Rightarrow> bool" where
  "update_map_postcond m1 m2 result \<longleftrightarrow>
    update_map_pairwise_le (map_entries result) \<and>
    list_all
      (\<lambda>x. update_map_find result (fst x) = Some (snd x))
      (map_entries m2) \<and>
    list_all
      (\<lambda>x.
        case update_map_find m2 (fst x) of
          Some v \<Rightarrow> True
        | None \<Rightarrow>
            update_map_find result (fst x) = Some (snd x))
      (map_entries m1) \<and>
    list_all
      (\<lambda>x.
        case update_map_find m1 (fst x) of
          Some v \<Rightarrow>
            (case update_map_find m2 (fst x) of
               Some v' \<Rightarrow> snd x = v'
             | None \<Rightarrow> snd x = v)
        | None \<Rightarrow>
            update_map_find m2 (fst x) = Some (snd x))
      (map_entries result)"

theorem update_map_spec_satisfied:
  assumes "update_map_precond m1 m2"
  shows "update_map_postcond m1 m2 (update_map m1 m2)"
  sorry

end
