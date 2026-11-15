(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/avl/avl_AVL_balanceqtvc: an AVL-tree balancing verification condition
  with the source aggregation laws and recursive representation invariants,
  covering height bounds and sequence preservation for single and double
  rotations. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory optionTheory pairTheory;

Datatype:
  avl_model_tree =
    AvlModelEmpty
  | AvlModelNode avl_model_tree 'node avl_model_tree num 'summary
End

val avl_seq_model_def = Define `
  (avl_seq_model AvlModelEmpty = []) /\
  (avl_seq_model (AvlModelNode left root right height summary) =
     APPEND (avl_seq_model left) (root :: avl_seq_model right))`;

val avl_real_height_def = Define `
  (avl_real_height AvlModelEmpty = (0 : int)) /\
  (avl_real_height (AvlModelNode left root right height summary) =
     1 + (if avl_real_height left < avl_real_height right
          then avl_real_height right
          else avl_real_height left))`;

val avl_balanced_def = Define `
  (avl_balanced balancing agg measure_closure AvlModelEmpty = T) /\
  (avl_balanced balancing agg measure_closure
      (AvlModelNode left root right height summary) =
     (&height =
        avl_real_height
          (AvlModelNode left root right height summary) /\
      summary =
        agg measure_closure
          (avl_seq_model
            (AvlModelNode left root right height summary)) /\
      -(&balancing) <=
        avl_real_height right - avl_real_height left /\
      avl_real_height right - avl_real_height left <= &balancing /\
      avl_balanced balancing agg measure_closure left /\
      avl_balanced balancing agg measure_closure right))`;

val avl_balance_vc =
  ``let node_model =
      \left : 'node list. \root : 'node. \right : 'node list.
        APPEND left (root :: right)
    in
    let expected_height =
      \left_height : int. \right_height : int.
        1 + (if left_height < right_height
             then right_height
             else left_height)
    in
    let within_balance =
      \balancing : num. \left_height : int. \right_height : int.
        -(&balancing) <= left_height - right_height /\
        left_height - right_height <= &balancing
    in
    let built_node =
      \seq : 'tree -> 'node list.
      \hgt : 'tree -> int.
      \out : 'tree. \left : 'tree. \root : 'node. \right : 'tree.
        seq out = node_model (seq left) root (seq right) /\
        hgt out = expected_height (hgt left) (hgt right)
    in
    let view_ok =
      \balancing : num.
      \agg : ('node -> 'summary) -> 'node list -> 'summary.
      \measure_closure : 'node -> 'summary.
      \seq : 'tree -> 'node list.
      \hgt : 'tree -> int.
      \whole : 'tree.
      \v.
        case v of
          NONE =>
            hgt whole = 0 /\
            seq whole = []
        | SOME (left, root, right, height, summary) =>
            seq whole = node_model (seq left) root (seq right) /\
            summary = agg measure_closure (seq whole) /\
            within_balance balancing (hgt left) (hgt right) /\
            hgt whole = &height /\
            &height = expected_height (hgt left) (hgt right)
    in
      !(balancing : num)
       (zero : 'summary)
       (op : 'summary -> 'summary -> 'summary)
       (agg : ('node -> 'summary) -> 'node list -> 'summary)
       (measure : 'node -> 'summary)
       (measure_closure : 'node -> 'summary)
       (repr : 'tree -> ('node, 'summary) avl_model_tree)
       (seq : 'tree -> 'node list)
       (hgt : 'tree -> int)
       (l : 'tree) (r : 'tree)
       (hl : int) (hr : int) (o1 : int)
       (d : 'node).
        (0 : int) < &balancing ==>
        (!a b c. op a (op b c) = op (op a b) c) ==>
        (!x. op x zero = x /\ x = op zero x) ==>
        (!f. agg f [] = zero) ==>
        (!s f. LENGTH s = 1 ==> agg f s = f (EL 0 s)) ==>
        (!f s1 s2.
           agg f (APPEND s1 s2) = op (agg f s1) (agg f s2)) ==>
        (!y. measure_closure y = measure y) ==>
        (!self.
           avl_balanced balancing agg measure_closure (repr self) /\
           seq self = avl_seq_model (repr self) /\
           hgt self = avl_real_height (repr self)) ==>
        (!a b.
           repr a = repr b /\
           seq a = seq b /\
           hgt a = hgt b ==>
           a = b) ==>
        -(&balancing) - 1 <= hgt l - hgt r ==>
        hgt l - hgt r <= &balancing + 1 ==>
        hl = hgt l ==>
        hr = hgt r ==>
        o1 = -hr ==>
        o1 <= hl - hr /\
        hl - hr <= hl /\
        !(df : int).
          df = hl - hr ==>
          ((if &balancing < df then
              !left_view.
                view_ok balancing agg measure_closure seq hgt l left_view ==>
                case left_view of
                  NONE => F
                | SOME (ll, ld, lr, left_height, left_summary) =>
                    !(lr_height : int).
                      lr_height = hgt lr ==>
                      !(ll_height : int).
                        ll_height = hgt ll ==>
                        if lr_height <= ll_height then
                          within_balance balancing (hgt lr) (hgt r) /\
                          !right_child : 'tree.
                            built_node seq hgt right_child lr d r ==>
                            within_balance balancing
                              (hgt ll) (hgt right_child)
                        else
                          !lr_view.
                            view_ok balancing agg measure_closure
                              seq hgt lr lr_view ==>
                            case lr_view of
                              NONE => F
                            | SOME
                                (lrl, lrd, lrr, lr_height, lr_summary) =>
                                within_balance balancing
                                  (hgt lrr) (hgt r) /\
                                !right_child : 'tree.
                                  built_node seq hgt
                                    right_child lrr d r ==>
                                  within_balance balancing
                                    (hgt ll) (hgt lrl) /\
                                  !left_child : 'tree.
                                    built_node seq hgt
                                      left_child ll ld lrl ==>
                                    within_balance balancing
                                      (hgt left_child) (hgt right_child)
            else
              !(negative_balancing : int).
                negative_balancing = -(&balancing) ==>
                if df < negative_balancing then
                  !right_view.
                    view_ok balancing agg measure_closure
                      seq hgt r right_view ==>
                    case right_view of
                      NONE => F
                    | SOME (rl, rd, rr, right_height, right_summary) =>
                        !(rl_height : int).
                          rl_height = hgt rl ==>
                          !(rr_height : int).
                            rr_height = hgt rr ==>
                            if rl_height <= rr_height then
                              within_balance balancing (hgt l) (hgt rl) /\
                              !left_child : 'tree.
                                built_node seq hgt left_child l d rl ==>
                                within_balance balancing
                                  (hgt left_child) (hgt rr)
                            else
                              !rl_view.
                                view_ok balancing agg measure_closure
                                  seq hgt rl rl_view ==>
                                case rl_view of
                                  NONE => F
                                | SOME
                                    (rll, rld, rlr, rl_height, rl_summary) =>
                                    within_balance balancing
                                      (hgt rlr) (hgt rr) /\
                                    !right_child : 'tree.
                                      built_node seq hgt
                                        right_child rlr rd rr ==>
                                      within_balance balancing
                                        (hgt l) (hgt rll) /\
                                      !left_child : 'tree.
                                        built_node seq hgt
                                          left_child l d rll ==>
                                        within_balance balancing
                                          (hgt left_child) (hgt right_child)
                else
                  within_balance balancing (hgt l) (hgt r)) /\
           !result : 'tree.
             (if &balancing < df then
                ?left_view.
                  view_ok balancing agg measure_closure
                    seq hgt l left_view /\
                  case left_view of
                    NONE => F
                  | SOME (ll, ld, lr, left_height, left_summary) =>
                      ?lr_height : int.
                        lr_height = hgt lr /\
                        ?ll_height : int.
                          ll_height = hgt ll /\
                          if lr_height <= ll_height then
                            ?right_child : 'tree.
                              built_node seq hgt right_child lr d r /\
                              built_node seq hgt result ll ld right_child
                          else
                            ?lr_view.
                              view_ok balancing agg measure_closure
                                seq hgt lr lr_view /\
                              case lr_view of
                                NONE => F
                              | SOME
                                  (lrl, lrd, lrr, lr_height, lr_summary) =>
                                  ?right_child : 'tree.
                                    built_node seq hgt
                                      right_child lrr d r /\
                                    ?left_child : 'tree.
                                      built_node seq hgt
                                        left_child ll ld lrl /\
                                      built_node seq hgt
                                        result left_child lrd right_child
              else
                ?negative_balancing : int.
                  negative_balancing = -(&balancing) /\
                  if df < negative_balancing then
                    ?right_view.
                      view_ok balancing agg measure_closure
                        seq hgt r right_view /\
                      case right_view of
                        NONE => F
                      | SOME (rl, rd, rr, right_height, right_summary) =>
                          ?rl_height : int.
                            rl_height = hgt rl /\
                            ?rr_height : int.
                              rr_height = hgt rr /\
                              if rl_height <= rr_height then
                                ?left_child : 'tree.
                                  built_node seq hgt left_child l d rl /\
                                  built_node seq hgt result left_child rd rr
                              else
                                ?rl_view.
                                  view_ok balancing agg measure_closure
                                    seq hgt rl rl_view /\
                                  case rl_view of
                                    NONE => F
                                  | SOME
                                      (rll, rld, rlr, rl_height, rl_summary) =>
                                      ?right_child : 'tree.
                                        built_node seq hgt
                                          right_child rlr rd rr /\
                                        ?left_child : 'tree.
                                          built_node seq hgt
                                            left_child l d rll /\
                                          built_node seq hgt
                                            result left_child rld right_child
                  else
                    built_node seq hgt result l d r)
             ==>
             seq result = node_model (seq l) d (seq r) /\
             (let expected = expected_height (hgt l) (hgt r) in
              let result_height = hgt result in
                (0 <= expected - result_height /\
                 expected - result_height <= 1) /\
                (within_balance balancing (hgt l) (hgt r) ==>
                 expected = result_height)))``;
