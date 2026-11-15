(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_modified_Top_shearsortqtvc: the complete
  verification condition for the modified ShearSort row and column loops,
  including snake ordering, multiplicity preservation, and inversion decrease.
  This file contains no proof.
*)

#print_length 0;;

let ntp4vc_sms_matrix_INDUCT,
    ntp4vc_sms_matrix_RECURSION =
  define_type
    "ntp4vc_sms_matrix =
       NTP4VCShearsortModifiedMatrix num num (int->int->int)";;

let ntp4vc_sms_rows =
  new_recursive_definition ntp4vc_sms_matrix_RECURSION
   `!r c e.
      ntp4vc_sms_rows (NTP4VCShearsortModifiedMatrix r c e) =
      (&r:int)`;;

let ntp4vc_sms_columns =
  new_recursive_definition ntp4vc_sms_matrix_RECURSION
   `!r c e.
      ntp4vc_sms_columns (NTP4VCShearsortModifiedMatrix r c e) =
      (&c:int)`;;

let ntp4vc_sms_elts =
  new_recursive_definition ntp4vc_sms_matrix_RECURSION
   `!r c e.
      ntp4vc_sms_elts (NTP4VCShearsortModifiedMatrix r c e) = e`;;

let ntp4vc_sms_numof = new_definition
 `ntp4vc_sms_numof (p:int->bool) (a:int) (b:int) =
    (&(CARD {i:int | a <= i /\ i < b /\ p i}):int)`;;

let ntp4vc_sms_mocc = new_definition
 `ntp4vc_sms_mocc (x:int) (m:ntp4vc_sms_matrix) =
    isum {i:int | (&0:int) <= i /\ i < ntp4vc_sms_rows m}
      (\i. ntp4vc_sms_numof
             (\j. ntp4vc_sms_elts m i j = x)
             (&0:int) (ntp4vc_sms_columns m))`;;

let ntp4vc_sms_cdiv = new_definition
 `ntp4vc_sms_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_sms_cmod = new_definition
 `ntp4vc_sms_cmod (n:int) (d:int) =
    n - d * ntp4vc_sms_cdiv n d`;;

let ntp4vc_sms_lt = new_definition
 `ntp4vc_sms_lt (i:int) (j:int) (k:int) (l:int) <=>
    i < k \/
    i = k /\
    (if ntp4vc_sms_cmod i (&2:int) = (&0:int)
     then j < l
     else l < j)`;;

let ntp4vc_sms_snake_order = new_definition
 `ntp4vc_sms_snake_order (m:ntp4vc_sms_matrix) <=>
    !i j k l:int.
      (&0:int) <= i /\ i < ntp4vc_sms_rows m
      ==>
      (&0:int) <= j /\ j < ntp4vc_sms_columns m
      ==>
      (&0:int) <= k /\ k < ntp4vc_sms_rows m
      ==>
      (&0:int) <= l /\ l < ntp4vc_sms_columns m
      ==>
      ntp4vc_sms_lt i j k l
      ==>
      ntp4vc_sms_elts m i j <= ntp4vc_sms_elts m k l`;;

let ntp4vc_sms_inversions = new_definition
 `ntp4vc_sms_inversions (m:ntp4vc_sms_matrix) =
    isum {i:int | (&0:int) <= i /\ i < ntp4vc_sms_rows m}
      (\i. isum
        {j:int | (&0:int) <= j /\ j < ntp4vc_sms_columns m}
        (\j. isum
          {k:int | (&0:int) <= k /\ k < ntp4vc_sms_rows m}
          (\k. ntp4vc_sms_numof
                 (\l. ntp4vc_sms_lt i j k l /\
                      ntp4vc_sms_elts m k l <
                      ntp4vc_sms_elts m i j)
                 (&0:int) (ntp4vc_sms_columns m))))`;;

let ntp4vc_sms_sorted_row = new_definition
 `ntp4vc_sms_sorted_row
    (m:ntp4vc_sms_matrix) (row:int) (ascending:bool) <=>
    ((&0:int) <= row /\ row < ntp4vc_sms_rows m) /\
    (if ascending = T then
       !j l:int.
         (&0:int) <= j /\ j <= l /\ l < ntp4vc_sms_columns m
         ==> ntp4vc_sms_elts m row j <= ntp4vc_sms_elts m row l
     else
       !j l:int.
         (&0:int) <= j /\ j <= l /\ l < ntp4vc_sms_columns m
         ==> ntp4vc_sms_elts m row l <= ntp4vc_sms_elts m row j)`;;

let ntp4vc_sms_sorted_column = new_definition
 `ntp4vc_sms_sorted_column
    (m:ntp4vc_sms_matrix) (column:int) <=>
    ((&0:int) <= column /\ column < ntp4vc_sms_columns m) /\
    (!i k:int.
       (&0:int) <= i /\ i <= k /\ k < ntp4vc_sms_rows m
       ==> ntp4vc_sms_elts m i column <=
           ntp4vc_sms_elts m k column)`;;

let ntp4vc_sms_same_shape = new_definition
 `ntp4vc_sms_same_shape
    (current:ntp4vc_sms_matrix)
    (previous:ntp4vc_sms_matrix) <=>
    ntp4vc_sms_rows current = ntp4vc_sms_rows previous /\
    ntp4vc_sms_columns current = ntp4vc_sms_columns previous`;;

let ntp4vc_sms_occ_preserved = new_definition
 `ntp4vc_sms_occ_preserved
    (current:ntp4vc_sms_matrix)
    (original:ntp4vc_sms_matrix) <=>
    !x:int.
      ntp4vc_sms_mocc x current = ntp4vc_sms_mocc x original`;;

let ntp4vc_sms_rows_before = new_definition
 `ntp4vc_sms_rows_before
    (m:ntp4vc_sms_matrix) (limit:int) <=>
    !k:int.
      (&0:int) <= k /\ k < limit
      ==>
      ntp4vc_sms_sorted_row m k
        (if ntp4vc_sms_cmod k (&2:int) = (&0:int) then T else F)`;;

let ntp4vc_sms_columns_before = new_definition
 `ntp4vc_sms_columns_before
    (m:ntp4vc_sms_matrix) (limit:int) <=>
    !l:int.
      (&0:int) <= l /\ l < limit
      ==> ntp4vc_sms_sorted_column m l`;;

let ntp4vc_sms_all_entries_equal = new_definition
 `ntp4vc_sms_all_entries_equal
    (current:ntp4vc_sms_matrix)
    (previous:ntp4vc_sms_matrix) <=>
    !i j:int.
      (&0:int) <= i /\ i < ntp4vc_sms_rows current
      ==>
      (&0:int) <= j /\ j < ntp4vc_sms_columns current
      ==>
      ntp4vc_sms_elts current i j =
      ntp4vc_sms_elts previous i j`;;

let ntp4vc_sms_other_rows_equal = new_definition
 `ntp4vc_sms_other_rows_equal
    (current:ntp4vc_sms_matrix)
    (previous:ntp4vc_sms_matrix)
    (row:int) <=>
    !i j:int.
      (&0:int) <= i /\ i < ntp4vc_sms_rows current
      ==>
      (&0:int) <= j /\ j < ntp4vc_sms_columns current
      ==>
      ~(i = row)
      ==>
      ntp4vc_sms_elts current i j =
      ntp4vc_sms_elts previous i j`;;

let ntp4vc_sms_other_columns_equal = new_definition
 `ntp4vc_sms_other_columns_equal
    (current:ntp4vc_sms_matrix)
    (previous:ntp4vc_sms_matrix)
    (column:int) <=>
    !i j:int.
      (&0:int) <= i /\ i < ntp4vc_sms_rows current
      ==>
      (&0:int) <= j /\ j < ntp4vc_sms_columns current
      ==>
      ~(j = column)
      ==>
      ntp4vc_sms_elts current i j =
      ntp4vc_sms_elts previous i j`;;

let ntp4vc_sms_column_equal = new_definition
 `ntp4vc_sms_column_equal
    (current:ntp4vc_sms_matrix)
    (previous:ntp4vc_sms_matrix)
    (column:int) <=>
    !i:int.
      (&0:int) <= i /\ i < ntp4vc_sms_rows current
      ==>
      ntp4vc_sms_elts current i column =
      ntp4vc_sms_elts previous i column`;;

let ntp4vc_sms_original_bounds_order = new_definition
 `ntp4vc_sms_original_bounds_order
    (original:ntp4vc_sms_matrix)
    (current:ntp4vc_sms_matrix) <=>
    !i j k l:int.
      (((&0:int) <= i /\ i < ntp4vc_sms_columns original) /\
       ((&0:int) <= j /\ j < ntp4vc_sms_columns original) /\
       ((&0:int) <= k /\ k < ntp4vc_sms_columns original) /\
       ((&0:int) <= l /\ l < ntp4vc_sms_columns original) /\
       ntp4vc_sms_lt i j k l)
      ==>
      ntp4vc_sms_elts current i j <=
      ntp4vc_sms_elts current k l`;;

let ntp4vc_sms_column_update_post = new_definition
 `ntp4vc_sms_column_update_post
    (original:ntp4vc_sms_matrix)
    (column_base:ntp4vc_sms_matrix)
    (j:int)
    (nochange:bool)
    (current:ntp4vc_sms_matrix)
    (nch:bool) <=>
    if ~(nch = T) then
      (F = T
       ==> ntp4vc_sms_all_entries_equal current column_base) /\
      ntp4vc_sms_columns_before current (j + (&1:int)) /\
      ntp4vc_sms_occ_preserved current original /\
      ntp4vc_sms_inversions current <=
        ntp4vc_sms_inversions column_base /\
      (~(F = T)
       ==> ntp4vc_sms_inversions current <
           ntp4vc_sms_inversions column_base)
    else
      (nochange = T
       ==> ntp4vc_sms_all_entries_equal current column_base) /\
      ntp4vc_sms_columns_before current (j + (&1:int)) /\
      ntp4vc_sms_occ_preserved current original /\
      ntp4vc_sms_inversions current <=
        ntp4vc_sms_inversions column_base /\
      (~(nochange = T)
       ==> ntp4vc_sms_inversions current <
           ntp4vc_sms_inversions column_base)`;;

let ntp4vc_sms_column_iteration = new_definition
 `ntp4vc_sms_column_iteration
    (original:ntp4vc_sms_matrix)
    (column_base:ntp4vc_sms_matrix)
    (j:int)
    (nochange:bool)
    (previous:ntp4vc_sms_matrix) <=>
    ((&0:int) <= j /\ j < ntp4vc_sms_columns previous) /\
    (!current:ntp4vc_sms_matrix.
       ntp4vc_sms_same_shape current previous
       ==>
       (!nch:bool.
          ntp4vc_sms_other_columns_equal current previous j /\
          ntp4vc_sms_occ_preserved current previous /\
          (nch = T
           ==> ntp4vc_sms_column_equal current previous j) /\
          ntp4vc_sms_sorted_column current j /\
          ntp4vc_sms_inversions current <=
            ntp4vc_sms_inversions previous /\
          (~(nch = T)
           ==> ntp4vc_sms_inversions current <
               ntp4vc_sms_inversions previous)
          ==>
          ntp4vc_sms_column_update_post
            original column_base j nochange current nch))`;;

let ntp4vc_sms_column_completion = new_definition
 `ntp4vc_sms_column_completion
    (original:ntp4vc_sms_matrix)
    (cycle_base:ntp4vc_sms_matrix)
    (column_base:ntp4vc_sms_matrix)
    (o2:int)
    (nochange:bool)
    (current:ntp4vc_sms_matrix) <=>
    (nochange = T
     ==> ntp4vc_sms_all_entries_equal current column_base) /\
    ntp4vc_sms_columns_before current (o2 + (&1:int)) /\
    ntp4vc_sms_occ_preserved current original /\
    ntp4vc_sms_inversions current <=
      ntp4vc_sms_inversions column_base /\
    (~(nochange = T)
     ==> ntp4vc_sms_inversions current <
         ntp4vc_sms_inversions column_base)
    ==>
    if nochange = T then
      ntp4vc_sms_original_bounds_order original current /\
      ntp4vc_sms_snake_order current /\
      ntp4vc_sms_occ_preserved current original
    else
      ((&0:int) <= ntp4vc_sms_inversions cycle_base /\
       ntp4vc_sms_inversions current <
       ntp4vc_sms_inversions cycle_base) /\
      ntp4vc_sms_occ_preserved current original`;;

let ntp4vc_sms_column_phase = new_definition
 `ntp4vc_sms_column_phase
    (original:ntp4vc_sms_matrix)
    (cycle_base:ntp4vc_sms_matrix)
    (column_base:ntp4vc_sms_matrix) <=>
    let o2 = ntp4vc_sms_columns original - (&1:int) in
    (((&0:int) <= o2 + (&1:int)
      ==>
      (ntp4vc_sms_columns_before column_base (&0:int) /\
       ntp4vc_sms_occ_preserved column_base original /\
       ntp4vc_sms_inversions column_base <=
         ntp4vc_sms_inversions column_base) /\
      (!nochange:bool. !current:ntp4vc_sms_matrix.
         ntp4vc_sms_same_shape current column_base
         ==>
         (!j:int.
            (((&0:int) <= j /\ j <= o2) /\
             (nochange = T
              ==> ntp4vc_sms_all_entries_equal
                    current column_base) /\
             ntp4vc_sms_columns_before current j /\
             ntp4vc_sms_occ_preserved current original /\
             ntp4vc_sms_inversions current <=
               ntp4vc_sms_inversions column_base /\
             (~(nochange = T)
              ==> ntp4vc_sms_inversions current <
                  ntp4vc_sms_inversions column_base))
            ==>
            ntp4vc_sms_column_iteration
              original column_base j nochange current) /\
         ntp4vc_sms_column_completion
           original cycle_base column_base o2 nochange current)) /\
     (o2 + (&1:int) < (&0:int)
      ==>
      ntp4vc_sms_original_bounds_order original column_base /\
      ntp4vc_sms_snake_order column_base /\
      ntp4vc_sms_occ_preserved column_base original))`;;

let ntp4vc_sms_row_iteration = new_definition
 `ntp4vc_sms_row_iteration
    (original:ntp4vc_sms_matrix)
    (cycle_base:ntp4vc_sms_matrix)
    (i:int)
    (previous:ntp4vc_sms_matrix) <=>
    ~((&2:int) = (&0:int)) /\
    ((&0:int) <= i /\ i < ntp4vc_sms_rows previous) /\
    (!current:ntp4vc_sms_matrix.
       ntp4vc_sms_same_shape current previous
       ==>
       ntp4vc_sms_other_rows_equal current previous i /\
       ntp4vc_sms_occ_preserved current previous /\
       ntp4vc_sms_sorted_row current i
         (if ntp4vc_sms_cmod i (&2:int) = (&0:int) then T else F) /\
       ntp4vc_sms_inversions current <=
         ntp4vc_sms_inversions previous
       ==>
       ntp4vc_sms_rows_before current (i + (&1:int)) /\
       ntp4vc_sms_occ_preserved current original /\
       ntp4vc_sms_inversions current <=
         ntp4vc_sms_inversions cycle_base)`;;

let ntp4vc_sms_row_loop = new_definition
 `ntp4vc_sms_row_loop
    (original:ntp4vc_sms_matrix)
    (cycle_base:ntp4vc_sms_matrix)
    (o1:int) <=>
    !current:ntp4vc_sms_matrix.
      ntp4vc_sms_same_shape current cycle_base
      ==>
      (!i:int.
         (((&0:int) <= i /\ i <= o1) /\
          ntp4vc_sms_rows_before current i /\
          ntp4vc_sms_occ_preserved current original /\
          ntp4vc_sms_inversions current <=
            ntp4vc_sms_inversions cycle_base)
         ==>
         ntp4vc_sms_row_iteration
           original cycle_base i current) /\
      ((ntp4vc_sms_rows_before current (o1 + (&1:int)) /\
        ntp4vc_sms_occ_preserved current original /\
        ntp4vc_sms_inversions current <=
          ntp4vc_sms_inversions cycle_base)
       ==>
       ntp4vc_sms_column_phase original cycle_base current)`;;

let statement =
 `!m m1:ntp4vc_sms_matrix.
    ntp4vc_sms_rows m = ntp4vc_sms_columns m
    ==>
    ntp4vc_sms_rows m1 = ntp4vc_sms_rows m
    ==>
    ntp4vc_sms_columns m1 = ntp4vc_sms_columns m
    ==>
    ntp4vc_sms_occ_preserved m1 m
    ==>
    let o1 = ntp4vc_sms_columns m - (&1:int) in
    (((&0:int) <= o1 + (&1:int)
      ==>
      (ntp4vc_sms_rows_before m1 (&0:int) /\
       ntp4vc_sms_occ_preserved m1 m /\
       ntp4vc_sms_inversions m1 <= ntp4vc_sms_inversions m1) /\
      ntp4vc_sms_row_loop m m1 o1) /\
     (o1 + (&1:int) < (&0:int)
      ==> ntp4vc_sms_column_phase m m1 m1))`;;
