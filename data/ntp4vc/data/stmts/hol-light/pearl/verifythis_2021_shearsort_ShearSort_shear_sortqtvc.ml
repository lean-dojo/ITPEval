(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_shearsort_ShearSort_shear_sortqtvc: the complete
  ShearSort verification condition for logarithmic phase bounds, row and
  column sorting, zero-one separation, and preservation of matrix
  multiplicities. This file contains no proof.
*)

let ntp4vc_shearsort_matrix_INDUCT,
    ntp4vc_shearsort_matrix_RECURSION =
  define_type
    "ntp4vc_shearsort_matrix =
       NTP4VCShearSortMatrix num num (int->int->int)";;

let ntp4vc_shearsort_rows =
  new_recursive_definition ntp4vc_shearsort_matrix_RECURSION
   `!r c e.
      ntp4vc_shearsort_rows (NTP4VCShearSortMatrix r c e) =
      (&r:int)`;;

let ntp4vc_shearsort_columns =
  new_recursive_definition ntp4vc_shearsort_matrix_RECURSION
   `!r c e.
      ntp4vc_shearsort_columns (NTP4VCShearSortMatrix r c e) =
      (&c:int)`;;

let ntp4vc_shearsort_elts =
  new_recursive_definition ntp4vc_shearsort_matrix_RECURSION
   `!r c e.
      ntp4vc_shearsort_elts (NTP4VCShearSortMatrix r c e) = e`;;

let ntp4vc_shearsort_numof = new_definition
 `ntp4vc_shearsort_numof (p:int->bool) (a:int) (b:int) =
    (&(CARD {i:int | a <= i /\ i < b /\ p i}):int)`;;

let ntp4vc_shearsort_mocc = new_definition
 `ntp4vc_shearsort_mocc
    (x:int) (e:int->int->int) (r:int) (c:int) =
    isum {i:int | (&0:int) <= i /\ i < r}
      (\i. ntp4vc_shearsort_numof (\j. e i j = x) (&0:int) c)`;;

let ntp4vc_shearsort_permut = new_definition
 `ntp4vc_shearsort_permut
    (a:int->int) (b:int->int) (l:int) (u:int) <=>
    !v:int.
      ntp4vc_shearsort_numof (\i. a i = v) l u =
      ntp4vc_shearsort_numof (\i. b i = v) l u`;;

let ntp4vc_shearsort_power = new_definition
 `ntp4vc_shearsort_power (base:int) (exponent:int) =
    base pow
      (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let ntp4vc_shearsort_cdiv = new_definition
 `ntp4vc_shearsort_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let ntp4vc_shearsort_cmod = new_definition
 `ntp4vc_shearsort_cmod (n:int) (d:int) =
    n - d * ntp4vc_shearsort_cdiv n d`;;

let ntp4vc_shearsort_same_shape = new_definition
 `ntp4vc_shearsort_same_shape
    (m1:ntp4vc_shearsort_matrix)
    (m2:ntp4vc_shearsort_matrix) <=>
    ntp4vc_shearsort_rows m1 = ntp4vc_shearsort_rows m2 /\
    ntp4vc_shearsort_columns m1 = ntp4vc_shearsort_columns m2`;;

let ntp4vc_shearsort_row_order = new_definition
 `ntp4vc_shearsort_row_order
    (r:int->int) (ascending:bool) (c:int) <=>
    !j k:int.
      (&0:int) <= j /\ j <= k /\ k < c
      ==> if ascending then r j <= r k else r k <= r j`;;

let ntp4vc_shearsort_row_snake = new_definition
 `ntp4vc_shearsort_row_snake
    (e:int->int->int) (n:int) (c:int) <=>
    !i j k:int.
      ((&0:int) <= i /\ i < n) /\
      (&0:int) <= j /\ j <= k /\ k < c
      ==>
      if ntp4vc_shearsort_cmod i (&2:int) = (&0:int)
      then e i j <= e i k
      else e i k <= e i j`;;

let ntp4vc_shearsort_cross_sorted = new_definition
 `ntp4vc_shearsort_cross_sorted
    (e:int->int->int) (n:int) (c:int) <=>
    !i j1 j2 k:int.
      ((&0:int) <= i /\ i < k /\ k < n) /\
      ((&0:int) <= j1 /\ j1 < c) /\
      (&0:int) <= j2 /\ j2 < c
      ==> e i j1 <= e k j2`;;

let ntp4vc_shearsort_row_permuted = new_definition
 `ntp4vc_shearsort_row_permuted
    (m2:ntp4vc_shearsort_matrix)
    (m1:ntp4vc_shearsort_matrix) <=>
    !i:int.
      (&0:int) <= i /\ i < ntp4vc_shearsort_rows m2
      ==>
      ntp4vc_shearsort_permut
        (ntp4vc_shearsort_elts m2 i)
        (ntp4vc_shearsort_elts m1 i)
        (&0:int) (ntp4vc_shearsort_columns m2)`;;

let ntp4vc_shearsort_column_permuted = new_definition
 `ntp4vc_shearsort_column_permuted
    (m3:ntp4vc_shearsort_matrix)
    (m2:ntp4vc_shearsort_matrix) <=>
    !j:int.
      (&0:int) <= j /\ j < ntp4vc_shearsort_columns m3
      ==>
      ntp4vc_shearsort_permut
        (\i. ntp4vc_shearsort_elts m3 i j)
        (\i. ntp4vc_shearsort_elts m2 i j)
        (&0:int) (ntp4vc_shearsort_rows m3)`;;

let ntp4vc_shearsort_column_sorted = new_definition
 `ntp4vc_shearsort_column_sorted
    (m:ntp4vc_shearsort_matrix) <=>
    !i j k:int.
      ((&0:int) <= i /\ i <= k /\ k < ntp4vc_shearsort_rows m) /\
      (&0:int) <= j /\ j < ntp4vc_shearsort_columns m
      ==> ntp4vc_shearsort_elts m i j <=
          ntp4vc_shearsort_elts m k j`;;

let ntp4vc_shearsort_bounds = new_definition
 `ntp4vc_shearsort_bounds
    (e:int->int->int)
    (zeros:int->int) (ones:int->int)
    (width:int) (n:int) (c:int) <=>
    (!v:int.
       (&0:int) <= zeros v /\ zeros v <= ones v /\ ones v <= n) /\
    (!v:int. ones v <= zeros v + width) /\
    (!v i j:int.
       ((&0:int) <= i /\ i < zeros v) /\
       (&0:int) <= j /\ j < c
       ==> e i j <= v) /\
    (!v i j:int.
       (ones v <= i /\ i < n) /\
       (&0:int) <= j /\ j < c
       ==> v < e i j)`;;

let ntp4vc_shearsort_occ_preserved = new_definition
 `ntp4vc_shearsort_occ_preserved
    (original:ntp4vc_shearsort_matrix)
    (current:ntp4vc_shearsort_matrix)
    (n:int) (c:int) <=>
    !x:int.
      ntp4vc_shearsort_mocc
        x (ntp4vc_shearsort_elts original) n c =
      ntp4vc_shearsort_mocc
        x (ntp4vc_shearsort_elts current) n c`;;

let ntp4vc_shearsort_log_bound = new_definition
 `ntp4vc_shearsort_log_bound (k:int) (ind:int) (n:int) <=>
    (&0:int) < k /\
    (k - (&1:int)) *
        ntp4vc_shearsort_power (&2:int) ind < n /\
    n <= k * ntp4vc_shearsort_power (&2:int) ind`;;

let ntp4vc_shearsort_select_contract = new_definition
 `ntp4vc_shearsort_select_contract
    (r1:int->int) (r2:int->int)
    (v:int) (c:int) (result:bool) <=>
    (result
     ==> !i:int.
           (&0:int) <= i /\ i < c
           ==> r1 i <= v \/ r2 i <= v) /\
    (~result
     ==> !i:int.
           (&0:int) <= i /\ i < c
           ==> v < r1 i \/ v < r2 i)`;;

let ntp4vc_shearsort_select_vc = new_definition
 `ntp4vc_shearsort_select_vc (v:int) (c:int) <=>
    !r1 r2:int->int. !b:bool.
      ntp4vc_shearsort_row_order r1 b c /\
      ntp4vc_shearsort_row_order r2 (~b) c
      ==>
      if ~b then
        (((&0:int) <= (if b then (&0:int) else (&1:int)) /\
          (if T then (&0:int) else (&1:int)) <
          (if b then (&0:int) else (&1:int))) /\
         ntp4vc_shearsort_row_order r2 T c /\
         ntp4vc_shearsort_row_order r1 F c) /\
        (!result:bool.
           ntp4vc_shearsort_select_contract r2 r1 v c result
           ==>
           ntp4vc_shearsort_select_contract r1 r2 v c result)
      else
        (((&0:int) <= (&0:int) /\ (&0:int) <= c) /\
         (!j:int.
            (&0:int) <= j /\ j < (&0:int)
            ==> r1 j <= v /\ v < r2 j)) /\
        (!i:int.
           (((&0:int) <= i /\ i <= c) /\
            (!j:int.
               (&0:int) <= j /\ j < i
               ==> r1 j <= v /\ v < r2 j))
           ==>
           !o3:bool.
             (o3 =
                if ~(i = c) then
                  if r1 i <= v then
                    if v < r2 i then T else F
                  else F
                else F)
             ==>
             if o3 then
               ((&0:int) <= c - i /\
                c - (i + (&1:int)) < c - i) /\
               ((&0:int) <= i + (&1:int) /\
                i + (&1:int) <= c) /\
               (!j:int.
                  (&0:int) <= j /\ j < i + (&1:int)
                  ==> r1 j <= v /\ v < r2 j)
             else
               !result:bool.
                 (result =
                    if i = c then T
                    else if r2 i <= v then T else F)
                 ==>
                 ntp4vc_shearsort_select_contract
                   r1 r2 v c result)`;;

let ntp4vc_shearsort_pair_spec = new_definition
 `ntp4vc_shearsort_pair_spec
    (e:int->int->int)
    (nz:int) (no:int) (kd:int) (n:int) (c:int) (v:int) <=>
    (&0:int) <= nz /\ nz <= no /\ no <= n /\
    no <= nz + kd /\
    (!j:int.
       (&0:int) <= j /\ j < c
       ==>
       nz <=
         ntp4vc_shearsort_numof
           (\row. e row j <= v) (&0:int) n /\
       n - no <=
         ntp4vc_shearsort_numof
           (\row. v < e row j) (&0:int) n)`;;

let ntp4vc_shearsort_nzo_invariant = new_definition
 `ntp4vc_shearsort_nzo_invariant
    (e:int->int->int)
    (z:int) (ob:int) (nz:int) (no:int) (idx:int)
    (n:int) (c:int) (v:int) <=>
    (z <= idx /\ idx <= ob) /\
    (z <= nz /\ no <= ob) /\
    idx - z = (&2:int) * (nz - z + ob - no) /\
    (!j:int.
       (&0:int) <= j /\ j < c
       ==>
       nz <=
         ntp4vc_shearsort_numof
           (\row. e row j <= v) (&0:int) idx /\
       n - no <=
         ntp4vc_shearsort_numof
           (\row. v < e row j) (&0:int) idx +
         ntp4vc_shearsort_numof
           (\row. v < e row j) ob n)`;;

let ntp4vc_shearsort_nzo_vc = new_definition
 `ntp4vc_shearsort_nzo_vc
    (e:int->int->int)
    (zeros:int->int) (ones:int->int)
    (kd:int) (n:int) (c:int) (v:int) <=>
    let z = zeros v in
    let ob = ones v in
    ntp4vc_shearsort_nzo_invariant e z ob z ob z n c v /\
    (!idx no nz:int.
       ntp4vc_shearsort_nzo_invariant
         e z ob nz no idx n c v
       ==>
       if idx + (&1:int) < ob then
         ntp4vc_shearsort_select_vc v c /\
         ~((&2:int) = (&0:int)) /\
         (let ascending =
            ntp4vc_shearsort_cmod idx (&2:int) = (&0:int) in
          let r1 = e idx in
          let r2 = e (idx + (&1:int)) in
          ntp4vc_shearsort_row_order r1 ascending c /\
          ntp4vc_shearsort_row_order r2 (~ascending) c /\
          (!result:bool.
             ntp4vc_shearsort_select_contract
               r1 r2 v c result
             ==>
             if result then
               ((&0:int) <= ob - idx /\
                ob - (idx + (&2:int)) < ob - idx) /\
               ntp4vc_shearsort_nzo_invariant
                 e z ob (nz + (&1:int)) no
                 (idx + (&2:int)) n c v
             else
               ((&0:int) <= ob - idx /\
                ob - (idx + (&2:int)) < ob - idx) /\
               ntp4vc_shearsort_nzo_invariant
                 e z ob nz (no - (&1:int))
                 (idx + (&2:int)) n c v))
       else
         ntp4vc_shearsort_pair_spec e nz no kd n c v)`;;

let ntp4vc_shearsort_aux_up = new_definition
 `ntp4vc_shearsort_aux_up
    (e:int->int->int) (n:int) (c:int) <=>
    !v i j:int.
      ((&0:int) <= i /\ i < n) /\
      ((&0:int) <
         ntp4vc_shearsort_numof
           (\row. e row j <= v) (i + (&1:int)) n /\
       (&0:int) <= j /\ j < c) /\
      v < e i j
      ==>
      let next = i + (&1:int) in
      ((&0:int) <= n - i /\ n - next < n - i) /\
      ((&0:int) <= next /\ next < n) /\
      ((&0:int) <
         ntp4vc_shearsort_numof
           (\row. e row j <= v) (next + (&1:int)) n /\
       (&0:int) <= j /\ j < c) /\
      v < e next j`;;

let ntp4vc_shearsort_aux_down = new_definition
 `ntp4vc_shearsort_aux_down
    (e:int->int->int) (n:int) (c:int) <=>
    !v i j:int.
      ((&0:int) <= i /\ i < n) /\
      ((&0:int) <
         ntp4vc_shearsort_numof
           (\row. v < e row j) (&0:int) i /\
       (&0:int) <= j /\ j < c) /\
      e i j <= v
      ==>
      let previous = i - (&1:int) in
      ((&0:int) <= i /\ previous < i) /\
      ((&0:int) <= previous /\ previous < n) /\
      ((&0:int) <
         ntp4vc_shearsort_numof
           (\row. v < e row j) (&0:int) previous /\
       (&0:int) <= j /\ j < c) /\
      e previous j <= v`;;

let ntp4vc_shearsort_final = new_definition
 `ntp4vc_shearsort_final
    (m:ntp4vc_shearsort_matrix) <=>
    ntp4vc_shearsort_cross_sorted
      (ntp4vc_shearsort_elts m)
      (ntp4vc_shearsort_rows m)
      (ntp4vc_shearsort_columns m) /\
    ntp4vc_shearsort_row_snake
      (ntp4vc_shearsort_elts m)
      (ntp4vc_shearsort_rows m)
      (ntp4vc_shearsort_columns m)`;;

let ntp4vc_shearsort_column_phase = new_definition
 `ntp4vc_shearsort_column_phase
    (original:ntp4vc_shearsort_matrix)
    (m2:ntp4vc_shearsort_matrix)
    (zeros:int->int) (ones:int->int)
    (newz:int->int) (newo:int->int)
    (ind:int) (l:int) (kd:int) (n:int) (c:int) <=>
    (ind = l
     ==>
     ntp4vc_shearsort_bounds
       (ntp4vc_shearsort_elts m2)
       zeros ones (&1:int) n c) /\
    ((ind = l
      ==>
      ntp4vc_shearsort_cross_sorted
        (ntp4vc_shearsort_elts m2) n c)
     ==>
     !m3:ntp4vc_shearsort_matrix.
       ntp4vc_shearsort_same_shape m3 m2
       ==>
       ntp4vc_shearsort_column_permuted m3 m2 /\
       ntp4vc_shearsort_column_sorted m3
       ==>
       ntp4vc_shearsort_aux_up
         (ntp4vc_shearsort_elts m3) n c /\
       ntp4vc_shearsort_aux_down
         (ntp4vc_shearsort_elts m3) n c /\
       ntp4vc_shearsort_bounds
         (ntp4vc_shearsort_elts m3)
         newz newo kd n c /\
       ntp4vc_shearsort_log_bound kd (ind + (&1:int)) n /\
       (l < ind + (&1:int)
        ==>
        ntp4vc_shearsort_row_snake
          (ntp4vc_shearsort_elts m3) n c) /\
       ntp4vc_shearsort_occ_preserved
         original m3 n c)`;;

let ntp4vc_shearsort_projection_phase = new_definition
 `ntp4vc_shearsort_projection_phase
    (original:ntp4vc_shearsort_matrix)
    (m2:ntp4vc_shearsort_matrix)
    (e:int->int->int)
    (zeros:int->int) (ones:int->int)
    (ind:int) (l:int) (kd:int) (n:int) (c:int) <=>
    !nzo:int->int#int.
      (!v:int.
         ntp4vc_shearsort_pair_spec
           e (FST (nzo v)) (SND (nzo v)) kd n c v)
      ==>
      !v0:int.
        ntp4vc_shearsort_pair_spec
          e (FST (nzo v0)) (SND (nzo v0)) kd n c v0
        ==>
        (!result:int.
           result = FST (nzo v0)
           ==> result = FST (nzo v0)) /\
        (!newz:int->int.
           (!v:int. newz v = FST (nzo v))
           ==>
           !v1:int.
             ntp4vc_shearsort_pair_spec
               e (FST (nzo v1)) (SND (nzo v1)) kd n c v1
             ==>
             (!result:int.
                result = SND (nzo v1)
                ==> result = SND (nzo v1)) /\
             (!newo:int->int.
                (!v:int. newo v = SND (nzo v))
                ==>
                ntp4vc_shearsort_column_phase
                  original m2 zeros ones newz newo
                  ind l kd n c))`;;

let ntp4vc_shearsort_nzo_phase = new_definition
 `ntp4vc_shearsort_nzo_phase
    (original:ntp4vc_shearsort_matrix)
    (m2:ntp4vc_shearsort_matrix)
    (zeros:int->int) (ones:int->int)
    (ind:int) (l:int) (kd:int) (n:int) (c:int) <=>
    let e = ntp4vc_shearsort_elts m2 in
    (!v:int.
       ntp4vc_shearsort_nzo_vc
         e zeros ones kd n c v) /\
    ntp4vc_shearsort_projection_phase
      original m2 e zeros ones ind l kd n c`;;

let ntp4vc_shearsort_loop_body = new_definition
 `ntp4vc_shearsort_loop_body
    (original:ntp4vc_shearsort_matrix)
    (m1:ntp4vc_shearsort_matrix)
    (zeros:int->int) (ones:int->int)
    (k:int) (ind:int) (l:int) (n:int) (c:int) <=>
    !m2:ntp4vc_shearsort_matrix.
      ntp4vc_shearsort_same_shape m2 m1
      ==>
      ntp4vc_shearsort_row_permuted m2 m1 /\
      ntp4vc_shearsort_row_snake
        (ntp4vc_shearsort_elts m2)
        (ntp4vc_shearsort_rows m2)
        (ntp4vc_shearsort_columns m2)
      ==>
      ~((&2:int) = (&0:int)) /\
      (let kd =
         ntp4vc_shearsort_cdiv (k + (&1:int)) (&2:int) in
       ntp4vc_shearsort_nzo_phase
         original m2 zeros ones ind l kd n c)`;;

let ntp4vc_shearsort_loop_invariant = new_definition
 `ntp4vc_shearsort_loop_invariant
    (original:ntp4vc_shearsort_matrix)
    (m1:ntp4vc_shearsort_matrix)
    (zeros:int->int) (ones:int->int)
    (k:int) (ind:int) (l:int) (n:int) (c:int) <=>
    ((&0:int) <= ind /\ ind <= l) /\
    ntp4vc_shearsort_bounds
      (ntp4vc_shearsort_elts m1)
      zeros ones k n c /\
    ntp4vc_shearsort_log_bound k ind n /\
    (l < ind
     ==>
     ntp4vc_shearsort_row_snake
       (ntp4vc_shearsort_elts m1) n c) /\
    ntp4vc_shearsort_occ_preserved
      original m1 n c`;;

let ntp4vc_shearsort_post_loop = new_definition
 `ntp4vc_shearsort_post_loop
    (original:ntp4vc_shearsort_matrix)
    (m1:ntp4vc_shearsort_matrix)
    (zeros:int->int) (ones:int->int)
    (k:int) (l:int) (n:int) (c:int) <=>
    ntp4vc_shearsort_bounds
      (ntp4vc_shearsort_elts m1)
      zeros ones k n c /\
    ntp4vc_shearsort_log_bound k (l + (&1:int)) n /\
    (l < l + (&1:int)
     ==>
     ntp4vc_shearsort_row_snake
       (ntp4vc_shearsort_elts m1) n c) /\
    ntp4vc_shearsort_occ_preserved
      original m1 n c`;;

let ntp4vc_shearsort_completion = new_definition
 `ntp4vc_shearsort_completion
    (original:ntp4vc_shearsort_matrix)
    (m1:ntp4vc_shearsort_matrix)
    (n:int) (c:int) <=>
    ntp4vc_shearsort_cross_sorted
      (ntp4vc_shearsort_elts m1) n c
    ==>
    ntp4vc_shearsort_final m1 /\
    ntp4vc_shearsort_occ_preserved
      original m1
      (ntp4vc_shearsort_rows m1)
      (ntp4vc_shearsort_columns m1)`;;

let ntp4vc_shearsort_initial = new_definition
 `ntp4vc_shearsort_initial
    (m:ntp4vc_shearsort_matrix)
    (l:int) (n:int) (c:int) <=>
    ntp4vc_shearsort_bounds
      (ntp4vc_shearsort_elts m)
      (\v. (&0:int)) (\v. n) n n c /\
    ntp4vc_shearsort_log_bound n (&0:int) n /\
    (l < (&0:int)
     ==>
     ntp4vc_shearsort_row_snake
       (ntp4vc_shearsort_elts m) n c)`;;

let statement =
 `!m:ntp4vc_shearsort_matrix.
    let n = ntp4vc_shearsort_rows m in
    let c = ntp4vc_shearsort_columns m in
    if ~(n = (&0:int)) then
      let o1 = n - (&1:int) in
      (((&0:int) <= (&0:int) /\ (&0:int) <= o1) /\
       o1 * ntp4vc_shearsort_power (&2:int) (&0:int) < n /\
       n <=
         ntp4vc_shearsort_power (&2:int) (&0:int) *
         (o1 + (&1:int))) /\
      (!p l:int.
         (((&0:int) <= l /\ (&0:int) <= p) /\
          (~(l = (&0:int))
           ==>
           ntp4vc_shearsort_power
             (&2:int) (l - (&1:int)) <= n) /\
          p * ntp4vc_shearsort_power (&2:int) l < n /\
          n <=
            ntp4vc_shearsort_power (&2:int) l *
            (p + (&1:int)))
         ==>
         if ~(p = (&0:int)) then
           ~((&2:int) = (&0:int)) /\
           ((&0:int) <= p /\
            ntp4vc_shearsort_cdiv p (&2:int) < p) /\
           ((&0:int) <= l + (&1:int) /\
            (&0:int) <=
              ntp4vc_shearsort_cdiv p (&2:int)) /\
           (~(l + (&1:int) = (&0:int))
            ==>
            ntp4vc_shearsort_power
              (&2:int) (l + (&1:int) - (&1:int)) <= n) /\
           ntp4vc_shearsort_cdiv p (&2:int) *
             ntp4vc_shearsort_power
               (&2:int) (l + (&1:int)) < n /\
           n <=
             ntp4vc_shearsort_power
               (&2:int) (l + (&1:int)) *
             (ntp4vc_shearsort_cdiv p (&2:int) + (&1:int))
         else
           (!ones zeros:int->int.
            !m1:ntp4vc_shearsort_matrix.
              ntp4vc_shearsort_same_shape m1 m
              ==>
              ntp4vc_shearsort_bounds
                (ntp4vc_shearsort_elts m1)
                zeros ones (&1:int) n c
              ==>
              ntp4vc_shearsort_cross_sorted
                (ntp4vc_shearsort_elts m1) n c) /\
           ((&0:int) <= l + (&1:int)
            ==>
            ntp4vc_shearsort_initial m l n c /\
            (!ones zeros:int->int. !k:int.
             !m1:ntp4vc_shearsort_matrix.
               ntp4vc_shearsort_same_shape m1 m
               ==>
               (!ind:int.
                  ntp4vc_shearsort_loop_invariant
                    m m1 zeros ones k ind l n c
                  ==>
                  ntp4vc_shearsort_loop_body
                    m m1 zeros ones k ind l n c) /\
               (ntp4vc_shearsort_post_loop
                  m m1 zeros ones k l n c
                ==>
                ntp4vc_shearsort_bounds
                  (ntp4vc_shearsort_elts m1)
                  zeros ones (&1:int) n c /\
                ntp4vc_shearsort_completion
                  m m1 n c))) /\
           (l + (&1:int) < (&0:int)
            ==>
            ntp4vc_shearsort_bounds
              (ntp4vc_shearsort_elts m)
              (\v. (&0:int)) (\v. n) (&1:int) n c /\
            (ntp4vc_shearsort_cross_sorted
               (ntp4vc_shearsort_elts m) n c
             ==>
             ntp4vc_shearsort_final m)))
    else
      ntp4vc_shearsort_final m`;;
