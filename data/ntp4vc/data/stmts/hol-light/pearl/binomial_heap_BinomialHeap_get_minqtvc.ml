(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binomial_heap_BinomialHeap_get_minqtvc: a binomial-heap minimum
  verification condition showing that a recursive scan of a nonempty
  heap-ordered forest returns a stored element below every stored element.
  This file contains no proof.
*)

let ntp4vc_get_min_tree_INDUCT,ntp4vc_get_min_tree_RECURSION =
  define_type
    "ntp4vc_get_min_tree =
       NTP4VCGetMinTree A (ntp4vc_get_min_tree list) int";;

let statement =
 `!le:A->A->bool.
  !elem:A ntp4vc_get_min_tree->A.
  !le_roots:A->(A ntp4vc_get_min_tree)list->bool.
  !heaps:(A ntp4vc_get_min_tree)list->bool.
  !occ:A->(A ntp4vc_get_min_tree)list->int.
  !h:(A ntp4vc_get_min_tree)list.
    let mem =
      \(x:A) (forest:(A ntp4vc_get_min_tree)list).
        (&0:int) < occ x forest in
    let scan_contract =
      \(m:A) (forest:(A ntp4vc_get_min_tree)list).
        heaps forest
        ==>
        ((forest = [] \/
          (!t:A ntp4vc_get_min_tree.
           !tail:(A ntp4vc_get_min_tree)list.
             forest = CONS t tail
             ==>
             (!chosen:A.
                (if le (elem t) m
                 then chosen = elem t
                 else chosen = m)
                ==>
                heaps tail))) /\
         (!result:A.
            ((forest = [] /\ result = m) \/
             (?t:A ntp4vc_get_min_tree.
              ?tail:(A ntp4vc_get_min_tree)list.
              ?chosen:A.
                forest = CONS t tail /\
                (if le (elem t) m
                 then chosen = elem t
                 else chosen = m) /\
                (result = chosen \/ mem result tail) /\
                le result chosen /\
                (!x:A. mem x tail ==> le result x)))
            ==>
            (result = m \/ mem result forest) /\
            le result m /\
            (!x:A. mem x forest ==> le result x))) in
    let background =
      ((!x:A. le x x) /\
       (!x y z:A. le x y /\ le y z ==> le x z) /\
       (!x y:A. le x y \/ le y x) /\
       (!e:A.
        !children:(A ntp4vc_get_min_tree)list.
        !rank:int.
          elem (NTP4VCGetMinTree e children rank) = e) /\
       (!e:A. le_roots e [] <=> T) /\
       (!e:A.
        !t:A ntp4vc_get_min_tree.
        !tail:(A ntp4vc_get_min_tree)list.
          (le_roots e (CONS t tail) <=>
           le e (elem t) /\ le_roots e tail)) /\
       (heaps [] <=> T) /\
       (!e:A.
        !children:(A ntp4vc_get_min_tree)list.
        !rank:int.
        !tail:(A ntp4vc_get_min_tree)list.
          (heaps
             (CONS
               (NTP4VCGetMinTree e children rank)
               tail) <=>
           le_roots e children /\
           heaps children /\
           heaps tail)) /\
       (!x:A. occ x [] = (&0:int)) /\
       (!x y:A.
        !children:(A ntp4vc_get_min_tree)list.
        !rank:int.
        !tail:(A ntp4vc_get_min_tree)list.
          occ x
            (CONS
              (NTP4VCGetMinTree y children rank)
              tail) =
          (if x = y then (&1:int) else (&0:int)) +
          occ x children +
          occ x tail)) in
    background
    ==>
    heaps h
    ==>
    ~(h = [])
    ==>
    (?t:A ntp4vc_get_min_tree.
     ?tail:(A ntp4vc_get_min_tree)list.
       h = CONS t tail /\
       (!m:A.
        !forest:(A ntp4vc_get_min_tree)list.
          scan_contract m forest) /\
       heaps tail) /\
    (!result:A.
       (?t:A ntp4vc_get_min_tree.
        ?tail:(A ntp4vc_get_min_tree)list.
          h = CONS t tail /\
          (result = elem t \/ mem result tail) /\
          le result (elem t) /\
          (!x:A. mem x tail ==> le result x))
       ==>
       mem result h /\
       (!x:A. mem x h ==> le result x))`;;
