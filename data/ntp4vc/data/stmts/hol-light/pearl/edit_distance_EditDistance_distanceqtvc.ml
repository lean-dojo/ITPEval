(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/edit_distance_EditDistance_distanceqtvc: the dynamic-programming
  verification condition for computing a minimum insertion/deletion edit
  distance between suffixes of two words. This file contains no proof.
*)

let edit_distance_dist_RULES,
    edit_distance_dist_INDUCT,
    edit_distance_dist_CASES =
  new_inductive_definition
   `(edit_distance_dist ([]:A list) ([]:A list) (&0:int)) /\
    (!w1 w2:A list.
     !n:int.
     !a:A.
       edit_distance_dist w1 w2 n
       ==>
       edit_distance_dist (CONS a w1) w2 (n + (&1:int))) /\
    (!w1 w2:A list.
     !n:int.
     !a:A.
       edit_distance_dist w1 w2 n
       ==>
       edit_distance_dist w1 (CONS a w2) (n + (&1:int))) /\
    (!w1 w2:A list.
     !n:int.
     !a:A.
       edit_distance_dist w1 w2 n
       ==>
       edit_distance_dist (CONS a w1) (CONS a w2) n)`;;

let edit_distance_min_dist = new_definition
 `edit_distance_min_dist (w1:A list) (w2:A list) (n:int) <=>
    edit_distance_dist w1 w2 n /\
    (!m:int. edit_distance_dist w1 w2 m ==> n <= m)`;;

let edit_distance_nth_int = new_definition
 `edit_distance_nth_int (a:int list) (i:int) =
    if a = [] then (&0:int)
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else (&0:int)`;;

let edit_distance_nth_char = new_definition
 `edit_distance_nth_char (default:A) (a:A list) (i:int) =
    if a = [] then default
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else default`;;

let edit_distance_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:int. edit_distance_update_nat [] n x = []) /\
    (!h:int.
     !t:int list.
     !n:num.
     !x:int.
       edit_distance_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (edit_distance_update_nat t (PRE n) x))`;;

let edit_distance_update = new_definition
 `edit_distance_update (a:int list) (i:int) (x:int) =
    if i < (&0:int)
    then edit_distance_update_nat a 0 x
    else edit_distance_update_nat a (num_of_int i) x`;;

let edit_distance_int_min = new_definition
 `edit_distance_int_min (x:int) (y:int) =
    if x <= y then x else y`;;

let edit_distance_min_suffix = new_definition
 `edit_distance_min_suffix
    (suffix:A list->int->A list)
    (a1:A list) (a2:A list) (i:int) (j:int) (n:int) <=>
    edit_distance_min_dist (suffix a1 i) (suffix a2 j) n`;;

let edit_distance_after_update = new_definition
 `edit_distance_after_update
    (suffix:A list->int->A list)
    (w1:A list) (w2:A list)
    (n2:int) (i:int) (j:int)
    (before:int list) (after:int list) <=>
    (!k:int.
       j - (&1:int) < k /\ k <= n2
       ==>
       edit_distance_min_suffix suffix w1 w2 i k
         (edit_distance_nth_int after k)) /\
    (!k:int.
       (&0:int) <= k /\ k <= j - (&1:int)
       ==>
       edit_distance_min_suffix suffix w1 w2 (i + (&1:int)) k
         (edit_distance_nth_int after k)) /\
    edit_distance_min_suffix suffix w1 w2
      (i + (&1:int)) (j - (&1:int) + (&1:int))
      (edit_distance_nth_int before j)`;;

let edit_distance_cell_step = new_definition
 `edit_distance_cell_step
    (default:A)
    (suffix:A list->int->A list)
    (w1:A list) (w2:A list)
    (n2:int) (i:int) (j:int) (oldt:int) (row:int list) <=>
    ((&0:int) <= j /\ j < (&(LENGTH row):int)) /\
    ((&0:int) <= j /\ j < (&(LENGTH w2):int)) /\
    ((&0:int) <= i /\ i < (&(LENGTH w1):int)) /\
    (if edit_distance_nth_char default w1 i =
        edit_distance_nth_char default w2 j
     then
       ((&0:int) <= j /\ j < (&(LENGTH row):int)) /\
       (LENGTH (edit_distance_update row j oldt) = LENGTH row
        ==>
        (!r:int.
           edit_distance_nth_int
             (edit_distance_update row j oldt) r =
           (if r = j then oldt else edit_distance_nth_int row r))
        ==>
        edit_distance_after_update suffix w1 w2 n2 i j row
          (edit_distance_update row j oldt))
     else
       let o5 = j + (&1:int) in
       ((&0:int) <= o5 /\ o5 < (&(LENGTH row):int)) /\
       ((&0:int) <= j /\ j < (&(LENGTH row):int)) /\
       let o6 =
         edit_distance_int_min
           (edit_distance_nth_int row j)
           (edit_distance_nth_int row o5) + (&1:int) in
       ((&0:int) <= j /\ j < (&(LENGTH row):int)) /\
       (LENGTH (edit_distance_update row j o6) = LENGTH row
        ==>
        (!r:int.
           edit_distance_nth_int
             (edit_distance_update row j o6) r =
           (if r = j then o6 else edit_distance_nth_int row r))
        ==>
        edit_distance_after_update suffix w1 w2 n2 i j row
          (edit_distance_update row j o6)))`;;

let edit_distance_column_loop = new_definition
 `edit_distance_column_loop
    (default:A)
    (suffix:A list->int->A list)
    (w1:A list) (w2:A list)
    (n2:int) (i:int) (o4:int) (initial:int list) <=>
    !oldt:int.
    !row:int list.
      LENGTH row = LENGTH initial
      ==>
      ((!j:int.
          ((j <= o4 /\ (&0:int) <= j) /\
           (!k:int.
              j < k /\ k <= n2
              ==>
              edit_distance_min_suffix suffix w1 w2 i k
                (edit_distance_nth_int row k)) /\
           (!k:int.
              (&0:int) <= k /\ k <= j
              ==>
              edit_distance_min_suffix suffix w1 w2 (i + (&1:int)) k
                (edit_distance_nth_int row k)) /\
           edit_distance_min_suffix suffix w1 w2
             (i + (&1:int)) (j + (&1:int)) oldt)
          ==>
          edit_distance_cell_step
            default suffix w1 w2 n2 i j oldt row) /\
       (((!k:int.
            (&0:int) - (&1:int) < k /\ k <= n2
            ==>
            edit_distance_min_suffix suffix w1 w2 i k
              (edit_distance_nth_int row k)) /\
         (!k:int.
            (&0:int) <= k /\ k <= (&0:int) - (&1:int)
            ==>
            edit_distance_min_suffix suffix w1 w2 (i + (&1:int)) k
              (edit_distance_nth_int row k)) /\
         edit_distance_min_suffix suffix w1 w2
           (i + (&1:int))
           ((&0:int) - (&1:int) + (&1:int)) oldt)
        ==>
        (!j:int.
           (&0:int) <= j /\ j <= n2
           ==>
           edit_distance_min_suffix suffix w1 w2
             (i - (&1:int) + (&1:int)) j
             (edit_distance_nth_int row j))))`;;

let edit_distance_row_step = new_definition
 `edit_distance_row_step
    (default:A)
    (suffix:A list->int->A list)
    (w1:A list) (w2:A list)
    (n2:int) (i:int) (row:int list) <=>
    ((&0:int) <= n2 /\ n2 < (&(LENGTH row):int)) /\
    ((&0:int) <= n2 /\ n2 < (&(LENGTH row):int)) /\
    let o3 = edit_distance_nth_int row n2 + (&1:int) in
    ((&0:int) <= n2 /\ n2 < (&(LENGTH row):int)) /\
    (LENGTH (edit_distance_update row n2 o3) = LENGTH row
     ==>
     (!r:int.
        edit_distance_nth_int
          (edit_distance_update row n2 o3) r =
        (if r = n2 then o3 else edit_distance_nth_int row r))
     ==>
     let o4 = n2 - (&1:int) in
     (((&0:int) - (&1:int) <= o4
       ==>
       ((!k:int.
           o4 < k /\ k <= n2
           ==>
           edit_distance_min_suffix suffix w1 w2 i k
             (edit_distance_nth_int
               (edit_distance_update row n2 o3) k)) /\
        (!k:int.
           (&0:int) <= k /\ k <= o4
           ==>
           edit_distance_min_suffix suffix w1 w2 (i + (&1:int)) k
             (edit_distance_nth_int
               (edit_distance_update row n2 o3) k)) /\
        edit_distance_min_suffix suffix w1 w2
          (i + (&1:int)) (o4 + (&1:int))
          (edit_distance_nth_int row n2)) /\
       edit_distance_column_loop
         default suffix w1 w2 n2 i o4
         (edit_distance_update row n2 o3)) /\
      (o4 < (&0:int) - (&1:int)
       ==>
       (!j:int.
          (&0:int) <= j /\ j <= n2
          ==>
          edit_distance_min_suffix suffix w1 w2
            (i - (&1:int) + (&1:int)) j
            (edit_distance_nth_int
              (edit_distance_update row n2 o3) j)))))`;;

let edit_distance_outer_loop = new_definition
 `edit_distance_outer_loop
    (default:A)
    (suffix:A list->int->A list)
    (w1:A list) (w2:A list)
    (n1:int) (n2:int) (row:int list) <=>
    let o2 = n1 - (&1:int) in
    (((&0:int) - (&1:int) <= o2
      ==>
      (!j:int.
         (&0:int) <= j /\ j <= n2
         ==>
         edit_distance_min_suffix suffix w1 w2 (o2 + (&1:int)) j
           (edit_distance_nth_int row j)) /\
      (!next:int list.
         LENGTH next = LENGTH row
         ==>
         ((!i:int.
             ((i <= o2 /\ (&0:int) <= i) /\
              (!j:int.
                 (&0:int) <= j /\ j <= n2
                 ==>
                 edit_distance_min_suffix suffix w1 w2
                   (i + (&1:int)) j
                   (edit_distance_nth_int next j)))
             ==>
             edit_distance_row_step
               default suffix w1 w2 n2 i next) /\
          ((!j:int.
              (&0:int) <= j /\ j <= n2
              ==>
              edit_distance_min_suffix suffix w1 w2
                ((&0:int) - (&1:int) + (&1:int)) j
                (edit_distance_nth_int next j))
           ==>
           (((&0:int) <= (&0:int) /\
             (&0:int) < (&(LENGTH next):int)) /\
            edit_distance_min_dist
              (suffix w1 (&0:int)) (suffix w2 (&0:int))
              (edit_distance_nth_int next (&0:int))))))) /\
     (o2 < (&0:int) - (&1:int)
      ==>
      ((&0:int) <= (&0:int) /\
       (&0:int) < (&(LENGTH row):int)) /\
      edit_distance_min_dist
        (suffix w1 (&0:int)) (suffix w2 (&0:int))
        (edit_distance_nth_int row (&0:int))))`;;

let edit_distance_initialization = new_definition
 `edit_distance_initialization
    (default:A)
    (suffix:A list->int->A list)
    (w1:A list) (w2:A list)
    (n1:int) (n2:int) (row:int list) <=>
    (!j:int.
       (&0:int) <= j /\ j < (&0:int)
       ==>
       edit_distance_nth_int row j = n2 - j) /\
    (!next:int list.
       LENGTH next = LENGTH row
       ==>
       ((!i:int.
           (((&0:int) <= i /\ i <= n2) /\
            (!j:int.
               (&0:int) <= j /\ j < i
               ==>
               edit_distance_nth_int next j = n2 - j))
           ==>
           let o2 = n2 - i in
           ((&0:int) <= i /\ i < (&(LENGTH next):int)) /\
           (LENGTH (edit_distance_update next i o2) = LENGTH next
            ==>
            (!r:int.
               edit_distance_nth_int
                 (edit_distance_update next i o2) r =
               (if r = i then o2 else edit_distance_nth_int next r))
            ==>
            (!j:int.
               (&0:int) <= j /\ j < i + (&1:int)
               ==>
               edit_distance_nth_int
                 (edit_distance_update next i o2) j =
               n2 - j))) /\
        ((!j:int.
            (&0:int) <= j /\ j < n2 + (&1:int)
            ==>
            edit_distance_nth_int next j = n2 - j)
         ==>
         edit_distance_outer_loop
           default suffix w1 w2 n1 n2 next)))`;;

let statement =
 `!default:A.
  !suffix:A list->int->A list.
  !w1 w2:A list.
    ((!a:A list.
        suffix a (&(LENGTH a):int) = []) /\
     (!i:int.
      !a:A list.
        (&0:int) <= i /\ i < (&(LENGTH a):int)
        ==>
        suffix a i =
          CONS (edit_distance_nth_char default a i)
            (suffix a (i + (&1:int)))))
    ==>
    let n1 = (&(LENGTH w1):int) in
    let n2 = (&(LENGTH w2):int) in
    let o1 = n2 + (&1:int) in
    (&0:int) <= o1 /\
    (!row:int list.
       ((!i:int.
           (&0:int) <= i /\ i < o1
           ==>
           edit_distance_nth_int row i = (&0:int)) /\
        (&(LENGTH row):int) = o1)
       ==>
       (((&0:int) <= n2 + (&1:int)
         ==>
         edit_distance_initialization
           default suffix w1 w2 n1 n2 row) /\
        (n2 + (&1:int) < (&0:int)
         ==>
         edit_distance_outer_loop
           default suffix w1 w2 n1 n2 row)))`;;
