(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc: the
  Warshall transitive-closure verification condition over Boolean matrices,
  including the bounded-path relation and all three loop invariants. This file
  contains no proof.
*)

let warshall_rows = new_definition
 `warshall_rows (m:num#(num#(int->int->bool))) = (&(FST m):int)`;;

let warshall_columns = new_definition
 `warshall_columns (m:num#(num#(int->int->bool))) =
    (&(FST (SND m)):int)`;;

let warshall_elts = new_definition
 `warshall_elts (m:num#(num#(int->int->bool))) = SND (SND m)`;;

let warshall_same_shape = new_definition
 `warshall_same_shape
    (a:num#(num#(int->int->bool)))
    (b:num#(num#(int->int->bool))) <=>
    warshall_rows a = warshall_rows b /\
    warshall_columns a = warshall_columns b`;;

let warshall_valid_index = new_definition
 `warshall_valid_index
    (m:num#(num#(int->int->bool))) (i:int) (j:int) <=>
    (&0:int) <= i /\ i < warshall_rows m /\
    (&0:int) <= j /\ j < warshall_columns m`;;

let warshall_update_entry = new_definition
 `warshall_update_entry
    (a:int->int->bool) (i:int) (j:int) (v:bool) =
    \x y. if x = i /\ y = j then v else a x y`;;

let warshall_path_RULES,
    warshall_path_INDUCT,
    warshall_path_CASES =
  new_inductive_definition
   `(!m:num#(num#(int->int->bool)).
     !i j k:int.
       warshall_elts m i j
       ==> warshall_path m i j k) /\
    (!x k:int.
     !m:num#(num#(int->int->bool)).
     !i j:int.
       (&0:int) <= x /\
       x < k /\
       warshall_path m i x k /\
       warshall_path m x j k
       ==> warshall_path m i j k)`;;

let warshall_invariant = new_definition
 `warshall_invariant
    (m:num#(num#(int->int->bool)))
    (t:num#(num#(int->int->bool)))
    (n:int) (k:int) <=>
    !x y:int.
      (&0:int) <= x /\ x < n
      ==>
      (&0:int) <= y /\ y < n
      ==>
      (warshall_elts t x y <=> warshall_path m x y k)`;;

let warshall_row_invariant = new_definition
 `warshall_row_invariant
    (m:num#(num#(int->int->bool)))
    (t:num#(num#(int->int->bool)))
    (n:int) (k:int) (i:int) <=>
    !x y:int.
      (&0:int) <= x /\ x < n
      ==>
      (&0:int) <= y /\ y < n
      ==>
      (warshall_elts t x y <=>
       if x < i
       then warshall_path m x y (k + (&1:int))
       else warshall_path m x y k)`;;

let warshall_column_invariant = new_definition
 `warshall_column_invariant
    (m:num#(num#(int->int->bool)))
    (t:num#(num#(int->int->bool)))
    (n:int) (k:int) (i:int) (j:int) <=>
    !x y:int.
      (&0:int) <= x /\ x < n
      ==>
      (&0:int) <= y /\ y < n
      ==>
      (warshall_elts t x y <=>
       if x < i \/ x = i /\ y < j
       then warshall_path m x y (k + (&1:int))
       else warshall_path m x y k)`;;

let warshall_cell_obligation = new_definition
 `warshall_cell_obligation
    (m:num#(num#(int->int->bool)))
    (t3:num#(num#(int->int->bool)))
    (n:int) (k:int) (i:int) (j:int) <=>
    warshall_valid_index t3 i j /\
    let o4 = warshall_elts t3 i j in
    (~o4
     ==>
     warshall_valid_index t3 i k /\
     (warshall_elts t3 i k ==> warshall_valid_index t3 k j)) /\
    (!o5:bool.
       (if o4
        then o5
        else if warshall_elts t3 i k
             then (o5 <=> warshall_elts t3 k j)
             else ~o5)
       ==>
       warshall_valid_index t3 i j /\
       (!t4:num#(num#(int->int->bool)).
          warshall_same_shape t4 t3
          ==>
          warshall_elts t4 =
            warshall_update_entry (warshall_elts t3) i j o5
          ==>
          warshall_column_invariant
            m t4 n k i (j + (&1:int))))`;;

let warshall_column_loop = new_definition
 `warshall_column_loop
    (m:num#(num#(int->int->bool)))
    (t2:num#(num#(int->int->bool)))
    (n:int) (k:int) (i:int) <=>
    let o3 = n - (&1:int) in
    (((&0:int) <= o3 + (&1:int)
      ==>
      warshall_column_invariant m t2 n k i (&0:int) /\
      (!t3:num#(num#(int->int->bool)).
         warshall_same_shape t3 t2
         ==>
         (!j:int.
            ((&0:int) <= j /\ j <= o3) /\
            warshall_column_invariant m t3 n k i j
            ==>
            warshall_cell_obligation m t3 n k i j) /\
         (warshall_column_invariant
            m t3 n k i (o3 + (&1:int))
          ==>
          warshall_row_invariant
            m t3 n k (i + (&1:int))))) /\
     (o3 + (&1:int) < (&0:int)
      ==>
      warshall_row_invariant
        m t2 n k (i + (&1:int))))`;;

let warshall_row_loop = new_definition
 `warshall_row_loop
    (m:num#(num#(int->int->bool)))
    (t1:num#(num#(int->int->bool)))
    (n:int) (k:int) <=>
    let o2 = n - (&1:int) in
    (((&0:int) <= o2 + (&1:int)
      ==>
      warshall_row_invariant m t1 n k (&0:int) /\
      (!t2:num#(num#(int->int->bool)).
         warshall_same_shape t2 t1
         ==>
         (!i:int.
            ((&0:int) <= i /\ i <= o2) /\
            warshall_row_invariant m t2 n k i
            ==>
            warshall_column_loop m t2 n k i) /\
         (warshall_row_invariant
            m t2 n k (o2 + (&1:int))
          ==>
          warshall_invariant
            m t2 n (k + (&1:int))))) /\
     (o2 + (&1:int) < (&0:int)
      ==>
      warshall_invariant
        m t1 n (k + (&1:int))))`;;

let warshall_outer_loop = new_definition
 `warshall_outer_loop
    (m:num#(num#(int->int->bool)))
    (t:num#(num#(int->int->bool)))
    (n:int) <=>
    let o1 = n - (&1:int) in
    (((&0:int) <= o1 + (&1:int)
      ==>
      warshall_invariant m t n (&0:int) /\
      (!t1:num#(num#(int->int->bool)).
         warshall_same_shape t1 t
         ==>
         (!k:int.
            ((&0:int) <= k /\ k <= o1) /\
            warshall_invariant m t1 n k
            ==>
            warshall_row_loop m t1 n k) /\
         (warshall_invariant m t1 n (o1 + (&1:int))
          ==>
          warshall_invariant m t1 n n))) /\
     (o1 + (&1:int) < (&0:int)
      ==>
      warshall_invariant m t n n))`;;

let statement =
 `!m:num#(num#(int->int->bool)).
  !t:num#(num#(int->int->bool)).
    warshall_rows m = warshall_columns m
    ==>
    warshall_rows t = warshall_rows m
    ==>
    warshall_columns t = warshall_columns m
    ==>
    (!r:int.
       (&0:int) <= r /\ r < warshall_rows t
       ==>
       !c:int.
         (&0:int) <= c /\ c < warshall_columns t
         ==>
         warshall_elts t r c = warshall_elts m r c)
    ==>
    warshall_outer_loop m t (warshall_rows m)`;;
