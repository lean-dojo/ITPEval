(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_balanceqtvc: an AVL-tree balance verification condition
  for single and double rotations, sequence preservation, and bounded cached
  height change. This file contains no proof.
*)

let avl_balance_tree_INDUCT,avl_balance_tree_RECURSION = define_type
  "avl_balance_tree =
       AvlBalanceEmpty
     | AvlBalanceNode avl_balance_tree A avl_balance_tree num B";;

let statement =
 `!zero:C.
  !op:C->C->C.
  !agg:(A->C)->A list->C.
  !measure:A->C.
  !balancing:num.
  !measure_closure:A->C.
  !seq_model:(A,C)avl_balance_tree->A list.
  !real_height:(A,C)avl_balance_tree->int.
  !balanced:(A,C)avl_balance_tree->bool.
  !repr:B->(A,C)avl_balance_tree.
  !m1:B->A list#int.
  !l r:B.
  !hl hr o1:int.
  !d:A.
    let node_model =
      \(left:A list) (datum:A) (right:A list).
        APPEND left (CONS datum right) in
    let seq = \x:B. FST (m1 x) in
    let hgt = \x:B. SND (m1 x) in
    let payload =
      \view:(B#A#B#num#C)option. @p. view = SOME p in
    let left =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        left in
    let datum =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        datum in
    let right =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        right in
    let stored_height =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        height in
    let summary =
      \((left:B),(datum:A),(right:B),(height:num),(summary:C)).
        summary in
    let within =
      \(left:B) (right:B).
        --(&balancing:int) <= hgt left - hgt right /\
        hgt left - hgt right <= (&balancing:int) in
    let built =
      \(result:B) (left:B) (datum:A) (right:B).
        seq result = node_model (seq left) datum (seq right) /\
        hgt result =
          (&1:int) +
          (if hgt left < hgt right then hgt right else hgt left) in
    let view_fact =
      \(subject:B) (view:(B#A#B#num#C)option).
        if view = NONE then
          hgt subject = (&0:int) /\ seq subject = []
        else
          let p = payload view in
          let left1 = left p in
          let datum1 = datum p in
          let right1 = right p in
          let height1 = stored_height p in
          let summary1 = summary p in
          seq subject =
            node_model (seq left1) datum1 (seq right1) /\
          summary1 = agg measure_closure (seq subject) /\
          within left1 right1 /\
          hgt subject = (&height1:int) /\
          (&height1:int) =
            (&1:int) +
            (if hgt left1 < hgt right1
             then hgt right1 else hgt left1) in
    let left_double_safety =
      \(view:(B#A#B#num#C)option) (ll:B) (ld:A) (r:B) (d:A).
        if view = NONE then F
        else
          let p = payload view in
          let lrl = left p in
          let lrr = right p in
          within lrr r /\
          (!o6:B.
             built o6 lrr d r
             ==> within ll lrl /\
                 (!o7:B.
                    built o7 ll ld lrl
                    ==> within o7 o6)) in
    let left_safety =
      \(view:(B#A#B#num#C)option) (r:B) (d:A).
        if view = NONE then F
        else
          let p = payload view in
          let ll = left p in
          let ld = datum p in
          let lr = right p in
          !o3:int.
            o3 = hgt lr
            ==> !o4:int.
                  o4 = hgt ll
                  ==> if o3 <= o4 then
                        within lr r /\
                        (!o5:B.
                           built o5 lr d r
                           ==> within ll o5)
                      else
                        !o5:(B#A#B#num#C)option.
                          view_fact lr o5
                          ==> left_double_safety o5 ll ld r d in
    let left_operational =
      \(l:B) (r:B) (d:A).
        !view:(B#A#B#num#C)option.
          view_fact l view ==> left_safety view r d in
    let right_double_safety =
      \(view:(B#A#B#num#C)option) (l:B) (d:A) (rd:A) (rr:B).
        if view = NONE then F
        else
          let p = payload view in
          let rll = left p in
          let rlr = right p in
          within rlr rr /\
          (!o7:B.
             built o7 rlr rd rr
             ==> within l rll /\
                 (!o8:B.
                    built o8 l d rll
                    ==> within o8 o7)) in
    let right_safety =
      \(view:(B#A#B#num#C)option) (l:B) (d:A).
        if view = NONE then F
        else
          let p = payload view in
          let rl = left p in
          let rd = datum p in
          let rr = right p in
          !o4:int.
            o4 = hgt rl
            ==> !o5:int.
                  o5 = hgt rr
                  ==> if o4 <= o5 then
                        within l rl /\
                        (!o6:B.
                           built o6 l d rl
                           ==> within o6 rr)
                      else
                        !o6:(B#A#B#num#C)option.
                          view_fact rl o6
                          ==> right_double_safety o6 l d rd rr in
    let right_operational =
      \(l:B) (r:B) (d:A).
        !view:(B#A#B#num#C)option.
          view_fact r view ==> right_safety view l d in
    let nonleft_operational =
      \(df:int) (l:B) (r:B) (d:A).
        !o2:int.
          o2 = --(&balancing:int)
          ==> if df < o2 then right_operational l r d
              else within l r in
    let left_single_result =
      \(result:B) (ll:B) (ld:A) (lr:B) (r:B) (d:A).
        ?o5:B. built o5 lr d r /\ built result ll ld o5 in
    let left_double_result =
      \(result:B) (ll:B) (ld:A) (lr:B) (r:B) (d:A).
        ?view:(B#A#B#num#C)option.
          view_fact lr view /\ ~(view = NONE) /\
          let p = payload view in
          let lrl = left p in
          let lrd = datum p in
          let lrr = right p in
          ?o6:B.
            built o6 lrr d r /\
            ?o7:B.
              built o7 ll ld lrl /\
              built result o7 lrd o6 in
    let left_result =
      \(result:B) (l:B) (r:B) (d:A).
        ?view:(B#A#B#num#C)option.
          view_fact l view /\ ~(view = NONE) /\
          let p = payload view in
          let ll = left p in
          let ld = datum p in
          let lr = right p in
          ?o3:int.
            o3 = hgt lr /\
            ?o4:int.
              o4 = hgt ll /\
              if o3 <= o4 then
                left_single_result result ll ld lr r d
              else
                left_double_result result ll ld lr r d in
    let right_single_result =
      \(result:B) (l:B) (d:A) (rl:B) (rd:A) (rr:B).
        ?o6:B. built o6 l d rl /\ built result o6 rd rr in
    let right_double_result =
      \(result:B) (l:B) (d:A) (rl:B) (rd:A) (rr:B).
        ?view:(B#A#B#num#C)option.
          view_fact rl view /\ ~(view = NONE) /\
          let p = payload view in
          let rll = left p in
          let rld = datum p in
          let rlr = right p in
          ?o7:B.
            built o7 rlr rd rr /\
            ?o8:B.
              built o8 l d rll /\
              built result o8 rld o7 in
    let right_result =
      \(result:B) (l:B) (r:B) (d:A).
        ?view:(B#A#B#num#C)option.
          view_fact r view /\ ~(view = NONE) /\
          let p = payload view in
          let rl = left p in
          let rd = datum p in
          let rr = right p in
          ?o4:int.
            o4 = hgt rl /\
            ?o5:int.
              o5 = hgt rr /\
              if o4 <= o5 then
                right_single_result result l d rl rd rr
              else
                right_double_result result l d rl rd rr in
    let nonleft_result =
      \(df:int) (result:B) (l:B) (r:B) (d:A).
        ?o2:int.
          o2 = --(&balancing:int) /\
          if df < o2 then right_result result l r d
          else built result l d r in
    let final_result =
      \(result:B) (l:B) (r:B) (d:A).
        seq result = node_model (seq l) d (seq r) /\
        let hl1 = hgt l in
        let hr1 = hgt r in
        let expected =
          (&1:int) + (if hl1 < hr1 then hr1 else hl1) in
        let result_height = hgt result in
        ((&0:int) <= expected - result_height /\
         expected - result_height <= (&1:int)) /\
        (within l r ==> expected = result_height) in
    let background =
      ((!a b c:C. op a (op b c) = op (op a b) c) /\
      (!x:C. op x zero = x /\ x = op zero x) /\
      (!f:A->C. agg f [] = zero) /\
      (!s:A list. !f:A->C.
         (&(LENGTH s):int) = (&1:int)
         ==> agg f s = f (EL 0 s)) /\
      (!f:A->C. !s1 s2:A list.
         agg f (APPEND s1 s2) = op (agg f s1) (agg f s2)) /\
      (!y:A. measure_closure y = measure y) /\
      seq_model AvlBalanceEmpty = [] /\
      (!left1:(A,C)avl_balance_tree.
       !datum1:A.
       !right1:(A,C)avl_balance_tree.
       !height1:num.
       !summary1:C.
         seq_model
           (AvlBalanceNode left1 datum1 right1 height1 summary1) =
         node_model (seq_model left1) datum1 (seq_model right1)) /\
      real_height AvlBalanceEmpty = (&0:int) /\
      (!left1:(A,C)avl_balance_tree.
       !datum1:A.
       !right1:(A,C)avl_balance_tree.
       !height1:num.
       !summary1:C.
         real_height
           (AvlBalanceNode left1 datum1 right1 height1 summary1) =
         (&1:int) +
         (if real_height left1 < real_height right1
          then real_height right1 else real_height left1)) /\
      balanced AvlBalanceEmpty /\
      (!left1:(A,C)avl_balance_tree.
       !datum1:A.
       !right1:(A,C)avl_balance_tree.
       !height1:num.
       !summary1:C.
         (balanced
            (AvlBalanceNode left1 datum1 right1 height1 summary1) <=>
          (&height1:int) =
            real_height
              (AvlBalanceNode
                left1 datum1 right1 height1 summary1) /\
          summary1 =
            agg measure_closure
              (seq_model
                (AvlBalanceNode
                  left1 datum1 right1 height1 summary1)) /\
          (--(&balancing:int) <=
             real_height right1 - real_height left1 /\
           real_height right1 - real_height left1 <=
             (&balancing:int)) /\
          balanced left1 /\ balanced right1)) /\
      (!self:B.
         balanced (repr self) /\
         seq self = seq_model (repr self) /\
         hgt self = real_height (repr self)) /\
      (!a b:B.
         repr a = repr b /\ m1 a = m1 b ==> a = b) /\
      0 < balancing) in
    background
    ==> --(&balancing:int) - (&1:int) <= hgt l - hgt r
    ==> hgt l - hgt r <= (&balancing:int) + (&1:int)
    ==> hl = hgt l
    ==> hr = hgt r
    ==> o1 = --hr
    ==> o1 <= hl - hr /\
        hl - hr <= hl /\
        (!df:int.
           df = hl - hr
           ==> (if (&balancing:int) < df then left_operational l r d
                else nonleft_operational df l r d) /\
               (!result:B.
                  (if (&balancing:int) < df
                   then left_result result l r d
                   else nonleft_result df result l r d)
                  ==> final_result result l r d))`;;
