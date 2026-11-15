(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2017_maximum_sum_submatrix_Kadane2D_maximum_submatrixqtvc:
  the verification condition for Kadane's two-dimensional maximum-sum
  submatrix algorithm, including its row, column, and maximality invariants.
  This file contains no proof.
*)

let kadane2d_nth = new_definition
 `kadane2d_nth (a:int list) (i:int) =
    if i < (&0:int) then (&0:int)
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else (&0:int)`;;

let kadane2d_update = new_recursive_definition list_RECURSION
 `(!n x.
     kadane2d_update ([]:int list) n x = []) /\
  (!h t n x.
     kadane2d_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (kadane2d_update t (PRE n) x))`;;

let kadane2d_sum = new_definition
 `kadane2d_sum (f:int->int) (l:int) (h:int) =
    isum {i:int | l <= i /\ i < h} f`;;

let kadane2d_array_sum = new_definition
 `kadane2d_array_sum (a:int list) (l:int) (h:int) =
    kadane2d_sum (kadane2d_nth a) l h`;;

let kadane2d_matrix_sum = new_definition
 `kadane2d_matrix_sum
    (elts:int->int->int) (rl:int) (rh:int) (cl:int) (ch:int) =
    kadane2d_sum
      (\j. kadane2d_sum (\i. elts i j) rl rh)
      cl ch`;;

let kadane2d_candidate = new_definition
 `kadane2d_candidate
    (elts:int->int->int) (rows:int) (columns:int)
    (rlo:int) (rhi:int) (clo:int) (chi:int) (maxsum:int) <=>
    ((&0:int) <= rlo /\ rlo <= rhi /\ rhi <= rows) /\
    ((&0:int) <= clo /\ clo <= chi /\ chi <= columns) /\
    (maxsum = kadane2d_matrix_sum elts rlo rhi clo chi /\
     (&0:int) <= kadane2d_matrix_sum elts rlo rhi clo chi)`;;

let kadane2d_outer_bound = new_definition
 `kadane2d_outer_bound
    (elts:int->int->int) (rows:int) (columns:int)
    (next_row:int) (maxsum:int) <=>
    !rl' rh:int.
      ((&0:int) <= rl' /\ rl' < next_row)
      ==>
      (rl' <= rh /\ rh <= rows)
      ==>
      !cl ch:int.
        ((&0:int) <= cl /\ cl <= ch /\ ch <= columns)
        ==>
        kadane2d_matrix_sum elts rl' rh cl ch <= maxsum`;;

let kadane2d_inner_bound = new_definition
 `kadane2d_inner_bound
    (elts:int->int->int) (rows:int) (columns:int)
    (rl:int) (next_rh:int) (maxsum:int) <=>
    !rl' rh':int.
      ((&0:int) <= rl' /\ rl' <= rh' /\ rh' <= rows)
      ==>
      (rl' < rl \/ rl' = rl /\ rh' < next_rh)
      ==>
      !cl ch:int.
        ((&0:int) <= cl /\ cl <= ch /\ ch <= columns)
        ==>
        kadane2d_matrix_sum elts rl' rh' cl ch <= maxsum`;;

let kadane2d_all_bound = new_definition
 `kadane2d_all_bound
    (elts:int->int->int) (rows:int) (columns:int) (maxsum:int) <=>
    !rl rh:int.
      ((&0:int) <= rl /\ rl <= rh /\ rh <= rows)
      ==>
      !cl ch:int.
        ((&0:int) <= cl /\ cl <= ch /\ ch <= columns)
        ==>
        kadane2d_matrix_sum elts rl rh cl ch <= maxsum`;;

let kadane2d_column_values = new_definition
 `kadane2d_column_values
    (a:int list) (elts:int->int->int) (columns:int)
    (rl:int) (rh:int) <=>
    !j:int.
      ((&0:int) <= j /\ j < columns)
      ==>
      kadane2d_nth a j =
      kadane2d_sum (\i. elts i j) rl rh`;;

let kadane2d_column_invariant = new_definition
 `kadane2d_column_invariant
    (a:int list) (elts:int->int->int) (columns:int)
    (rl:int) (rh:int) (c:int) <=>
    (!j:int.
       ((&0:int) <= j /\ j < c)
       ==>
       kadane2d_nth a j =
       kadane2d_sum (\i. elts i j) rl rh) /\
    (!j:int.
       (c <= j /\ j < columns)
       ==>
       kadane2d_nth a j =
       kadane2d_sum (\i. elts i j) rl (rh - (&1:int)))`;;

let kadane2d_maximum_subarray = new_definition
 `kadane2d_maximum_subarray (a:int list) (lo:int) (hi:int) <=>
    ((&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH a):int)) /\
    (!l h:int.
       ((&0:int) <= l /\ l <= h /\ h <= (&(LENGTH a):int))
       ==>
       kadane2d_array_sum a l h <= kadane2d_array_sum a lo hi)`;;

let kadane2d_after_maximum_subarray = new_definition
 `kadane2d_after_maximum_subarray
    (a:int list) (elts:int->int->int) (rows:int) (columns:int)
    (rl:int) (rh:int)
    (rlo:int) (rhi:int) (clo:int) (chi:int) (maxsum:int)
    (lo:int) (hi:int) <=>
    if maxsum < kadane2d_array_sum a lo hi then
      kadane2d_candidate
        elts rows columns rl rh lo hi
        (kadane2d_array_sum a lo hi) /\
      kadane2d_inner_bound
        elts rows columns rl (rh + (&1:int))
        (kadane2d_array_sum a lo hi) /\
      kadane2d_column_values
        a elts columns rl (rh + (&1:int) - (&1:int))
    else
      kadane2d_candidate
        elts rows columns rlo rhi clo chi maxsum /\
      kadane2d_inner_bound
        elts rows columns rl (rh + (&1:int)) maxsum /\
      kadane2d_column_values
        a elts columns rl (rh + (&1:int) - (&1:int))`;;

let kadane2d_column_step = new_definition
 `kadane2d_column_step
    (a:int list) (elts:int->int->int) (rows:int) (columns:int)
    (rl:int) (rh:int) (c:int) <=>
    let o7 = rh - (&1:int) in
    (((&0:int) <= o7 /\ o7 < rows) /\
     ((&0:int) <= c /\ c < columns)) /\
    ((&0:int) <= c /\ c < (&(LENGTH a):int)) /\
    let o8 = kadane2d_nth a c + elts o7 c in
    ((&0:int) <= c /\ c < (&(LENGTH a):int)) /\
    (LENGTH (kadane2d_update a (num_of_int c) o8) = LENGTH a
     ==>
     kadane2d_nth (kadane2d_update a (num_of_int c) o8) =
       (\r. if r = c then o8 else kadane2d_nth a r)
     ==>
     kadane2d_column_invariant
       (kadane2d_update a (num_of_int c) o8)
       elts columns rl rh (c + (&1:int)))`;;

let statement =
 `!rows columns:int. !elts:int->int->int.
    ((&0:int) <= rows /\ (&0:int) <= columns)
    ==>
    let o1 = columns in
    (&0:int) <= o1 /\
    (!a:int list.
       ((!i:int.
           ((&0:int) <= i /\ i < o1)
           ==> kadane2d_nth a i = (&0:int)) /\
        (&(LENGTH a):int) = o1)
       ==>
       let o2 = rows - (&1:int) in
       (((&0:int) <= o2 + (&1:int)
         ==>
         (kadane2d_candidate
            elts rows columns
            (&0:int) (&0:int) (&0:int) (&0:int) (&0:int) /\
          kadane2d_outer_bound
            elts rows columns (&0:int) (&0:int)) /\
         (!chi clo rhi rlo maxsum:int. !a1:int list.
            LENGTH a1 = LENGTH a
            ==>
            ((!rl:int.
                (((&0:int) <= rl /\ rl <= o2) /\
                 kadane2d_candidate
                   elts rows columns rlo rhi clo chi maxsum /\
                 kadane2d_outer_bound
                   elts rows columns rl maxsum)
                ==>
                let o3 = columns in
                (((&0:int) <= (&0:int) /\
                  (&0:int) <= o3 /\
                  (&0:int) + o3 <= (&(LENGTH a1):int)) /\
                 (!a2:int list.
                    LENGTH a2 = LENGTH a1
                    ==>
                    ((!i:int.
                        (((&0:int) <= i /\ i < (&0:int)) \/
                         ((&0:int) + o3 <= i /\
                          i < (&(LENGTH a2):int)))
                        ==>
                        kadane2d_nth a2 i = kadane2d_nth a1 i) /\
                     (!i:int.
                        ((&0:int) <= i /\ i < (&0:int) + o3)
                        ==> kadane2d_nth a2 i = (&0:int)))
                    ==>
                    let o4 = rows in
                    let o5 = rl + (&1:int) in
                    ((o5 <= o4 + (&1:int)
                      ==>
                      (kadane2d_candidate
                         elts rows columns
                         rlo rhi clo chi maxsum /\
                       kadane2d_inner_bound
                         elts rows columns rl o5 maxsum /\
                       kadane2d_column_values
                         a2 elts columns rl (o5 - (&1:int))) /\
                      (!chi1 clo1 rhi1 rlo1 maxsum1:int.
                       !a3:int list.
                         LENGTH a3 = LENGTH a2
                         ==>
                         (!rh:int.
                            (((o5 <= rh /\ rh <= o4) /\
                              kadane2d_candidate
                                elts rows columns
                                rlo1 rhi1 clo1 chi1 maxsum1 /\
                              kadane2d_inner_bound
                                elts rows columns rl rh maxsum1 /\
                              kadane2d_column_values
                                a3 elts columns
                                rl (rh - (&1:int)))
                             ==>
                             let o6 = columns - (&1:int) in
                             (((&0:int) <= o6 + (&1:int)
                               ==>
                               kadane2d_column_invariant
                                 a3 elts columns rl rh (&0:int) /\
                               (!a4:int list.
                                  LENGTH a4 = LENGTH a3
                                  ==>
                                  ((!c:int.
                                      (((&0:int) <= c /\ c <= o6) /\
                                       kadane2d_column_invariant
                                         a4 elts columns rl rh c)
                                      ==>
                                      kadane2d_column_step
                                        a4 elts rows columns rl rh c) /\
                                   (kadane2d_column_invariant
                                      a4 elts columns rl rh
                                      (o6 + (&1:int))
                                    ==>
                                    !lo hi:int.
                                      kadane2d_maximum_subarray a4 lo hi
                                      ==>
                                      kadane2d_after_maximum_subarray
                                        a4 elts rows columns rl rh
                                        rlo1 rhi1 clo1 chi1 maxsum1
                                        lo hi)))) /\
                              (o6 + (&1:int) < (&0:int)
                               ==>
                               !lo hi:int.
                                 kadane2d_maximum_subarray a3 lo hi
                                 ==>
                                 kadane2d_after_maximum_subarray
                                   a3 elts rows columns rl rh
                                   rlo1 rhi1 clo1 chi1 maxsum1
                                   lo hi)))) /\
                              ((kadane2d_candidate
                                  elts rows columns
                                  rlo1 rhi1 clo1 chi1 maxsum1 /\
                                kadane2d_inner_bound
                                  elts rows columns
                                  rl (o4 + (&1:int)) maxsum1 /\
                                kadane2d_column_values
                                  a3 elts columns rl
                                  (o4 + (&1:int) - (&1:int)))
                               ==>
                               kadane2d_candidate
                                 elts rows columns
                                 rlo1 rhi1 clo1 chi1 maxsum1 /\
                               kadane2d_outer_bound
                                 elts rows columns
                                 (rl + (&1:int)) maxsum1))) /\
                     (o4 + (&1:int) < o5
                      ==>
                      kadane2d_candidate
                        elts rows columns
                        rlo rhi clo chi maxsum /\
                      kadane2d_outer_bound
                        elts rows columns
                        (rl + (&1:int)) maxsum)))))) /\
             ((kadane2d_candidate
                 elts rows columns rlo rhi clo chi maxsum /\
               kadane2d_outer_bound
                 elts rows columns (o2 + (&1:int)) maxsum)
              ==>
              ((&0:int) <= rlo /\ rlo <= rhi /\ rhi <= rows) /\
              ((&0:int) <= clo /\ clo <= chi /\ chi <= columns) /\
              maxsum = kadane2d_matrix_sum
                         elts rlo rhi clo chi /\
              kadane2d_all_bound
                elts rows columns maxsum))) /\
        (o2 + (&1:int) < (&0:int)
         ==>
         (((&0:int) <= (&0:int) /\
           (&0:int) <= (&0:int) /\
           (&0:int) <= rows) /\
          ((&0:int) <= (&0:int) /\
           (&0:int) <= (&0:int) /\
           (&0:int) <= columns) /\
          (&0:int) =
            kadane2d_matrix_sum
              elts (&0:int) (&0:int) (&0:int) (&0:int) /\
          kadane2d_all_bound
            elts rows columns (&0:int)))))`;;
