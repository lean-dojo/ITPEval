(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc: the
  verification condition for enumerating valid red-and-black tile colorings
  of lengths through 50 by finite-set dynamic programming. This file contains
  no proof.
*)

let ntp4vc_colored_color_INDUCT,ntp4vc_colored_color_RECURSION = define_type
  "ntp4vc_colored_color =
       NTP4VC_COLORED_Red
     | NTP4VC_COLORED_Black";;

let ntp4vc_colored_nth = new_definition
 `ntp4vc_colored_nth (xs:A list) (i:int) =
    if (&0:int) <= i /\ num_of_int i < LENGTH xs
    then EL (num_of_int i) xs
    else ARB`;;

let ntp4vc_colored_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       ntp4vc_colored_update_nat [] n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       ntp4vc_colored_update_nat (CONS h t) n x =
       if n = 0
       then CONS x t
       else CONS h (ntp4vc_colored_update_nat t (PRE n) x))`;;

let ntp4vc_colored_update = new_definition
 `ntp4vc_colored_update (xs:A list) (i:int) (x:A) =
    if (&0:int) <= i /\ num_of_int i < LENGTH xs
    then ntp4vc_colored_update_nat xs (num_of_int i) x
    else xs`;;

let ntp4vc_colored_create_nat =
  new_recursive_definition num_RECURSION
   `(!f:int->ntp4vc_colored_color.
       ntp4vc_colored_create_nat 0 f = []) /\
    (!n:num.
     !f:int->ntp4vc_colored_color.
       ntp4vc_colored_create_nat (SUC n) f =
       APPEND (ntp4vc_colored_create_nat n f) [f (&n:int)])`;;

let ntp4vc_colored_create = new_definition
 `ntp4vc_colored_create
    (n:int) (f:int->ntp4vc_colored_color) =
    if n < (&0:int)
    then []
    else ntp4vc_colored_create_nat (num_of_int n) f`;;

let ntp4vc_colored_tworedneighbors = new_definition
 `ntp4vc_colored_tworedneighbors
    (c:ntp4vc_colored_color list) (i:int) <=>
    (ntp4vc_colored_nth c (i - (&2:int)) = NTP4VC_COLORED_Red /\
     ntp4vc_colored_nth c (i - (&1:int)) = NTP4VC_COLORED_Red /\
     (&2:int) <= i) \/
    (ntp4vc_colored_nth c (i - (&1:int)) = NTP4VC_COLORED_Red /\
     ntp4vc_colored_nth c (i + (&1:int)) = NTP4VC_COLORED_Red /\
     (&1:int) <= i /\
     i <= (&(LENGTH c):int) - (&2:int)) \/
    (ntp4vc_colored_nth c (i + (&1:int)) = NTP4VC_COLORED_Red /\
     ntp4vc_colored_nth c (i + (&2:int)) = NTP4VC_COLORED_Red /\
     i <= (&(LENGTH c):int) - (&3:int))`;;

let ntp4vc_colored_valid = new_definition
 `ntp4vc_colored_valid (c:ntp4vc_colored_color list) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH c):int)
      ==> ntp4vc_colored_nth c i = NTP4VC_COLORED_Red
      ==> ntp4vc_colored_tworedneighbors c i`;;

let ntp4vc_colored_finsets =
  new_recursive_definition list_RECURSION
   `(ntp4vc_colored_finsets
       ([]:(ntp4vc_colored_color list->bool) list) <=> T) /\
    (!s:ntp4vc_colored_color list->bool.
     !sets:(ntp4vc_colored_color list->bool) list.
       ntp4vc_colored_finsets (CONS s sets) <=>
       FINITE s /\ ntp4vc_colored_finsets sets)`;;

let ntp4vc_colored_mapaddleft = new_definition
 `ntp4vc_colored_mapaddleft
    (addleft_closure:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (s:ntp4vc_colored_color list->bool) (nr:int) =
    IMAGE (addleft_closure nr) s`;;

let ntp4vc_colored_update_cont = new_definition
 `ntp4vc_colored_update_cont
    (xs:A list) (i:int) (x:A) (p:bool) <=>
    LENGTH
      (ntp4vc_colored_update xs i x) =
      LENGTH xs
    ==>
    (\j:int.
       ntp4vc_colored_nth
         (ntp4vc_colored_update xs i x) j) =
      (\j:int. if j = i then x else ntp4vc_colored_nth xs j)
    ==>
    p`;;

let ntp4vc_colored_state = new_definition
 `ntp4vc_colored_state
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) (bound:int) <=>
    (!c:ntp4vc_colored_color list.
       (&0:int) <= (&(LENGTH c):int) /\
       (&(LENGTH c):int) < bound
       ==> ntp4vc_colored_valid c
       ==> ntp4vc_colored_nth sets (&(LENGTH c):int) c) /\
    (!c:ntp4vc_colored_color list.
     !i:int.
       (&0:int) <= i /\ i < bound
       ==> ntp4vc_colored_nth sets i c
       ==> (&(LENGTH c):int) = i /\ ntp4vc_colored_valid c) /\
    (!i:int.
       (&0:int) <= i /\ i < bound
       ==> ntp4vc_colored_nth count i =
           (&(CARD (ntp4vc_colored_nth sets i)):int))`;;

let ntp4vc_colored_bucket_state = new_definition
 `ntp4vc_colored_bucket_state
    (first_black_tile:ntp4vc_colored_color list->int)
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) (n:int) (threshold:int) <=>
    ntp4vc_colored_state sets count n /\
    (!c:ntp4vc_colored_color list.
       ntp4vc_colored_nth sets n c <=>
       (&(LENGTH c):int) = n /\
       ntp4vc_colored_valid c /\
       first_black_tile c < threshold) /\
    ntp4vc_colored_nth count n =
      (&(CARD (ntp4vc_colored_nth sets n)):int)`;;

let ntp4vc_colored_final = new_definition
 `ntp4vc_colored_final
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) <=>
    ((&(LENGTH count):int) = (&51:int) /\
     (&51:int) = (&(LENGTH sets):int)) /\
    (!i:int.
       (&0:int) <= i /\ i <= (&50:int)
       ==> !c:ntp4vc_colored_color list.
             (&(LENGTH c):int) = i
             ==> (ntp4vc_colored_valid c <=>
                  ntp4vc_colored_nth sets i c)) /\
    (!i:int.
       (&0:int) <= i /\ i < (&50:int)
       ==> ntp4vc_colored_nth count i =
           (&(CARD (ntp4vc_colored_nth sets i)):int))`;;

let ntp4vc_colored_inner_step = new_definition
 `ntp4vc_colored_inner_step
    (first_black_tile:ntp4vc_colored_color list->int)
    (addleft_closure:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) (n:int) (k:int) <=>
    let o10 = n - k - (&1:int) in
    ((&0:int) <= o10 /\ o10 < (&(LENGTH count):int)) /\
    ((&0:int) <= n /\ n < (&(LENGTH count):int)) /\
    let o11 =
      ntp4vc_colored_nth count n + ntp4vc_colored_nth count o10 in
    ((&0:int) <= n /\ n < (&(LENGTH count):int)) /\
    ntp4vc_colored_update_cont count n o11
      (let count' =
         ntp4vc_colored_update count n o11 in
       let o12 = n - k - (&1:int) in
       ((&0:int) <= o12 /\ o12 < (&(LENGTH sets):int)) /\
       let ns =
         ntp4vc_colored_mapaddleft addleft_closure
           (ntp4vc_colored_nth sets o12) k in
       ((&0:int) <= n /\ n < (&(LENGTH sets):int)) /\
       let o13 = ntp4vc_colored_nth sets n in
       (!x:ntp4vc_colored_color list. o13 x ==> ~ns x) /\
       let o14 = o13 UNION ns in
       (&(CARD o14):int) = (&(CARD o13):int) + (&(CARD ns):int)
       ==>
       ((&0:int) <= n /\ n < (&(LENGTH sets):int)) /\
       ntp4vc_colored_update_cont sets n o14
         (let sets' =
            ntp4vc_colored_update sets n o14 in
          ntp4vc_colored_bucket_state
            first_black_tile sets' count' n (k + (&1:int))))`;;

let ntp4vc_colored_add_red = new_definition
 `ntp4vc_colored_add_red
    (red:int->ntp4vc_colored_color)
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) (n:int) <=>
    (&0:int) <= n /\
    let r = ntp4vc_colored_create n red in
    ((&(LENGTH r):int) = n /\
     (!i:int.
        (&0:int) <= i /\ i < n
        ==> ntp4vc_colored_nth r i = red i))
    ==>
    (let sr = r INSERT EMPTY in
     ((&0:int) <= n /\ n < (&(LENGTH count):int)) /\
     let o11 = ntp4vc_colored_nth count n + (&1:int) in
     ((&0:int) <= n /\ n < (&(LENGTH count):int)) /\
     ntp4vc_colored_update_cont count n o11
       (let count' =
          ntp4vc_colored_update count n o11 in
        ((&0:int) <= n /\ n < (&(LENGTH sets):int)) /\
        let o12 = ntp4vc_colored_nth sets n in
        (!x:ntp4vc_colored_color list. o12 x ==> ~sr x) /\
        let o13 = o12 UNION sr in
        (&(CARD o13):int) = (&(CARD o12):int) + (&(CARD sr):int)
        ==>
        ((&0:int) <= n /\ n < (&(LENGTH sets):int)) /\
        ntp4vc_colored_update_cont sets n o13
          (let sets' =
             ntp4vc_colored_update sets n o13 in
           ntp4vc_colored_state sets' count' (n + (&1:int)))))`;;

let ntp4vc_colored_outer_step = new_definition
 `ntp4vc_colored_outer_step
    (first_black_tile:ntp4vc_colored_color list->int)
    (addleft_closure:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (fc5:int->ntp4vc_colored_color)
    (fc6:int->ntp4vc_colored_color)
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) (n:int) <=>
    let o5 = n - (&1:int) in
    ((&0:int) <= o5 /\ o5 < (&(LENGTH count):int)) /\
    let o6 = ntp4vc_colored_nth count o5 in
    ((&0:int) <= n /\ n < (&(LENGTH count):int)) /\
    ntp4vc_colored_update_cont count n o6
      (let count' =
         ntp4vc_colored_update count n o6 in
       let o7 = n - (&1:int) in
       ((&0:int) <= o7 /\ o7 < (&(LENGTH sets):int)) /\
       let o8 =
         ntp4vc_colored_mapaddleft addleft_closure
           (ntp4vc_colored_nth sets o7) (&0:int) in
       ((&0:int) <= n /\ n < (&(LENGTH sets):int)) /\
       ntp4vc_colored_update_cont sets n o8
         (let sets' =
            ntp4vc_colored_update sets n o8 in
          let o9 = n - (&1:int) in
          (((&3:int) <= o9 + (&1:int)
            ==>
            ntp4vc_colored_bucket_state
              first_black_tile sets' count' n (&3:int) /\
            (!sets2:(ntp4vc_colored_color list->bool) list.
             !count2:int list.
               ntp4vc_colored_finsets sets2
               ==>
               LENGTH sets2 = LENGTH sets'
               ==>
               LENGTH count2 = LENGTH count'
               ==>
               ((!k:int.
                   (((&3:int) <= k /\ k <= o9) /\
                    ntp4vc_colored_bucket_state
                      first_black_tile sets2 count2 n k)
                   ==>
                   ntp4vc_colored_inner_step
                     first_black_tile addleft_closure
                     sets2 count2 n k) /\
                (ntp4vc_colored_bucket_state
                   first_black_tile sets2 count2 n (o9 + (&1:int))
                 ==>
                 ntp4vc_colored_add_red fc5 sets2 count2 n))))
           /\
           (o9 + (&1:int) < (&3:int)
            ==>
            ntp4vc_colored_add_red fc6 sets' count' n))))`;;

let ntp4vc_colored_initialized = new_definition
 `ntp4vc_colored_initialized
    (first_black_tile:ntp4vc_colored_color list->int)
    (addleft_closure:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (fc5:int->ntp4vc_colored_color)
    (fc6:int->ntp4vc_colored_color)
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) <=>
    (((&4:int) <= (&50:int) + (&1:int)
      ==>
      ntp4vc_colored_state sets count (&4:int) /\
      (!sets1:(ntp4vc_colored_color list->bool) list.
       !count1:int list.
         ntp4vc_colored_finsets sets1
         ==>
         LENGTH sets1 = LENGTH sets
         ==>
         LENGTH count1 = LENGTH count
         ==>
         ((!n:int.
             (((&4:int) <= n /\ n <= (&50:int)) /\
              ntp4vc_colored_state sets1 count1 n)
             ==>
             ntp4vc_colored_outer_step
               first_black_tile addleft_closure fc5 fc6
               sets1 count1 n) /\
          (ntp4vc_colored_state
             sets1 count1 ((&50:int) + (&1:int))
           ==>
           ntp4vc_colored_final sets1 count1))))
     /\
     ((&50:int) + (&1:int) < (&4:int)
      ==> ntp4vc_colored_final sets count))`;;

let ntp4vc_colored_initialization = new_definition
 `ntp4vc_colored_initialization
    (first_black_tile:ntp4vc_colored_color list->int)
    (addleft_closure:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (fc:int->ntp4vc_colored_color)
    (fc1:int->ntp4vc_colored_color)
    (fc2:int->ntp4vc_colored_color)
    (fc3:int->ntp4vc_colored_color)
    (fc4:int->ntp4vc_colored_color)
    (fc5:int->ntp4vc_colored_color)
    (fc6:int->ntp4vc_colored_color)
    (sets:(ntp4vc_colored_color list->bool) list)
    (count:int list) <=>
    ((&0:int) <= (&0:int) /\ (&0:int) < (&(LENGTH count):int)) /\
    ntp4vc_colored_update_cont count (&0:int) (&1:int)
      (let count0 =
         ntp4vc_colored_update count (&0:int) (&1:int) in
       let o1 =
         ntp4vc_colored_create (&0:int) fc INSERT EMPTY in
       ((&0:int) <= (&0:int) /\ (&0:int) < (&(LENGTH sets):int)) /\
       ntp4vc_colored_update_cont sets (&0:int) o1
         (let sets0 = ntp4vc_colored_update sets (&0:int) o1 in
          ((&0:int) <= (&1:int) /\
           (&1:int) < (&(LENGTH count0):int)) /\
          ntp4vc_colored_update_cont count0 (&1:int) (&1:int)
            (let count1 =
               ntp4vc_colored_update count0 (&1:int) (&1:int) in
             let o2 =
               ntp4vc_colored_create (&1:int) fc1 INSERT EMPTY in
             ((&0:int) <= (&1:int) /\
              (&1:int) < (&(LENGTH sets0):int)) /\
             ntp4vc_colored_update_cont sets0 (&1:int) o2
               (let sets1 =
                  ntp4vc_colored_update sets0 (&1:int) o2 in
                ((&0:int) <= (&2:int) /\
                 (&2:int) < (&(LENGTH count1):int)) /\
                ntp4vc_colored_update_cont count1 (&2:int) (&1:int)
                  (let count2 =
                     ntp4vc_colored_update count1 (&2:int) (&1:int) in
                   let o3 =
                     ntp4vc_colored_create (&2:int) fc2 INSERT EMPTY in
                   ((&0:int) <= (&2:int) /\
                    (&2:int) < (&(LENGTH sets1):int)) /\
                   ntp4vc_colored_update_cont sets1 (&2:int) o3
                     (let sets2 =
                        ntp4vc_colored_update sets1 (&2:int) o3 in
                      ((&0:int) <= (&3:int) /\
                       (&3:int) < (&(LENGTH count2):int)) /\
                      ntp4vc_colored_update_cont
                        count2 (&3:int) (&2:int)
                        (let count3 =
                           ntp4vc_colored_update
                             count2 (&3:int) (&2:int) in
                         let o4 =
                           ntp4vc_colored_create (&3:int) fc3 INSERT
                           (ntp4vc_colored_create (&3:int) fc4 INSERT
                            EMPTY) in
                         ((&0:int) <= (&3:int) /\
                          (&3:int) < (&(LENGTH sets2):int)) /\
                         ntp4vc_colored_update_cont sets2 (&3:int) o4
                           (let sets3 =
                              ntp4vc_colored_update
                                sets2 (&3:int) o4 in
                            ntp4vc_colored_initialized
                              first_black_tile addleft_closure fc5 fc6
                              sets3 count3))))))))`;;

let ntp4vc_colored_context = new_definition
 `ntp4vc_colored_context
    (first_black_tile:ntp4vc_colored_color list->int)
    (addleft:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (addleft_closure:int->ntp4vc_colored_color list->
       ntp4vc_colored_color list)
    (fc:int->ntp4vc_colored_color)
    (fc1:int->ntp4vc_colored_color)
    (fc2:int->ntp4vc_colored_color)
    (fc3:int->ntp4vc_colored_color)
    (fc4:int->ntp4vc_colored_color)
    (fc5:int->ntp4vc_colored_color)
    (fc6:int->ntp4vc_colored_color) <=>
    (!c:ntp4vc_colored_color list.
       if LENGTH c = 0
       then first_black_tile c = (&0:int)
       else if HD c = NTP4VC_COLORED_Black
            then first_black_tile c = (&0:int)
            else first_black_tile c =
                 (&1:int) + first_black_tile (TL c)) /\
    (!c:ntp4vc_colored_color list.
       (&0:int) <= first_black_tile c /\
       first_black_tile c <= (&(LENGTH c):int)) /\
    (!j:int.
     !c:ntp4vc_colored_color list.
       (&0:int) <= j /\
       j < first_black_tile c /\
       first_black_tile c <= (&(LENGTH c):int)
       ==> ntp4vc_colored_nth c j = NTP4VC_COLORED_Red) /\
    (!c:ntp4vc_colored_color list.
       first_black_tile c < (&(LENGTH c):int)
       ==> ntp4vc_colored_nth c (first_black_tile c) =
           NTP4VC_COLORED_Black) /\
    (!c:ntp4vc_colored_color list.
       ntp4vc_colored_valid c
       ==> first_black_tile c = (&0:int) \/
           (&3:int) <= first_black_tile c) /\
    (!nr:int.
     !c:ntp4vc_colored_color list.
       if nr <= (&0:int)
       then addleft nr c = CONS NTP4VC_COLORED_Black c
       else addleft nr c =
            CONS NTP4VC_COLORED_Red
              (addleft (nr - (&1:int)) c)) /\
    (!nr:int.
     !c:ntp4vc_colored_color list.
       (&0:int) <= nr
       ==> (&(LENGTH (addleft nr c)):int) =
           (&(LENGTH c):int) + nr + (&1:int)) /\
    (!nr:int.
     !c:ntp4vc_colored_color list.
       addleft_closure nr c = addleft nr c) /\
    (!i:int. fc i = NTP4VC_COLORED_Black) /\
    (!i:int. fc1 i = NTP4VC_COLORED_Black) /\
    (!i:int. fc2 i = NTP4VC_COLORED_Black) /\
    (!i:int. fc3 i = NTP4VC_COLORED_Red) /\
    (!i:int. fc4 i = NTP4VC_COLORED_Black) /\
    (!i:int. fc5 i = NTP4VC_COLORED_Red) /\
    (!i:int. fc6 i = NTP4VC_COLORED_Red)`;;

let statement =
 `!first_black_tile:ntp4vc_colored_color list->int.
  !addleft:int->ntp4vc_colored_color list->ntp4vc_colored_color list.
  !addleft_closure:
     int->ntp4vc_colored_color list->ntp4vc_colored_color list.
  !fc fc1 fc2 fc3 fc4 fc5 fc6:int->ntp4vc_colored_color.
    ntp4vc_colored_context
      first_black_tile addleft addleft_closure
      fc fc1 fc2 fc3 fc4 fc5 fc6
    ==>
    ((&0:int) <= (&51:int)) /\
    (!count:int list.
       ((!i:int.
           (&0:int) <= i /\ i < (&51:int)
           ==> ntp4vc_colored_nth count i = (&0:int)) /\
        (&(LENGTH count):int) = (&51:int))
       ==>
       ((&0:int) <= (&51:int)) /\
       (!sets:(ntp4vc_colored_color list->bool) list.
          (ntp4vc_colored_finsets sets /\
           (!i:int.
              (&0:int) <= i /\ i < (&51:int)
              ==> ntp4vc_colored_nth sets i = EMPTY) /\
           (&(LENGTH sets):int) = (&51:int))
          ==>
          ntp4vc_colored_initialization
            first_black_tile addleft_closure
            fc fc1 fc2 fc3 fc4 fc5 fc6 sets count))`;;
