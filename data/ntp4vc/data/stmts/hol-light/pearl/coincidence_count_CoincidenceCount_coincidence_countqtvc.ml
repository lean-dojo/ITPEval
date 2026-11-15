(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/coincidence_count_CoincidenceCount_coincidence_countqtvc:
  a coincidence-count verification condition for two strictly increasing
  integer lists, preserving the cardinality of their common distinct suffix
  elements through the three comparison branches. This file contains no proof.
*)

let statement =
 `let nth_i =
    \(a:int list) (i:int).
      COND (i < (&0:int))
        (COND (a = []) (&0:int) (EL 0 a))
        (COND (num_of_int i < LENGTH a)
          (EL (num_of_int i) a) (&0:int)) in
  let increasing =
    \(a:int list).
      !i j:int.
        (&0:int) <= i /\ i < j /\ j < (&(LENGTH a):int)
        ==> nth_i a i < nth_i a j in
  let suffix =
    \(a:int list) (i:int). DROP (num_of_int i) a in
  let common_card =
    \(xs:int list) (ys:int list).
      CARD {x:int | MEM x xs /\ MEM x ys} in
  !a b:int list.
    increasing a ==>
    increasing b ==>
    ((&0:int) <= (&0:int) /\
     (&0:int) <= (&(LENGTH a):int) /\
     (&0:int) <= (&0:int) /\
     (&0:int) <= (&(LENGTH b):int) /\
     (&0:int) +
       (&(common_card (suffix a (&0:int)) (suffix b (&0:int))):int) =
       (&(common_card a b):int) /\
     (!c j i:int.
        (((&0:int) <= i /\ i <= (&(LENGTH a):int)) /\
         ((&0:int) <= j /\ j <= (&(LENGTH b):int)) /\
         c + (&(common_card (suffix a i) (suffix b j)):int) =
           (&(common_card a b):int))
        ==>
        (!o1:bool.
           COND (i < (&(LENGTH a):int))
             (o1 = COND (j < (&(LENGTH b):int)) T F)
             (o1 = F)
           ==>
           COND (o1 = T)
              (((&0:int) <= j /\ j < (&(LENGTH b):int)) /\
               ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
               COND (nth_i a i < nth_i b j)
                  (((&0:int) <=
                      (&(LENGTH a):int) - i +
                      (&(LENGTH b):int) - j /\
                    (&(LENGTH a):int) - (i + (&1:int)) +
                      (&(LENGTH b):int) - j <
                    (&(LENGTH a):int) - i +
                      (&(LENGTH b):int) - j) /\
                   ((&0:int) <= i + (&1:int) /\
                    i + (&1:int) <= (&(LENGTH a):int)) /\
                   ((&0:int) <= j /\ j <= (&(LENGTH b):int)) /\
                   c +
                     (&(common_card
                         (suffix a (i + (&1:int))) (suffix b j)):int) =
                     (&(common_card a b):int))
                  (((&0:int) <= j /\ j < (&(LENGTH b):int)) /\
                   ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
                   COND (nth_i b j < nth_i a i)
                      (((&0:int) <=
                          (&(LENGTH a):int) - i +
                          (&(LENGTH b):int) - j /\
                        (&(LENGTH a):int) - i +
                          (&(LENGTH b):int) - (j + (&1:int)) <
                        (&(LENGTH a):int) - i +
                          (&(LENGTH b):int) - j) /\
                       ((&0:int) <= i /\ i <= (&(LENGTH a):int)) /\
                       ((&0:int) <= j + (&1:int) /\
                        j + (&1:int) <= (&(LENGTH b):int)) /\
                       c +
                         (&(common_card
                             (suffix a i)
                             (suffix b (j + (&1:int)))):int) =
                         (&(common_card a b):int))
                      (((&0:int) <=
                          (&(LENGTH a):int) - i +
                          (&(LENGTH b):int) - j /\
                        (&(LENGTH a):int) - (i + (&1:int)) +
                          (&(LENGTH b):int) - (j + (&1:int)) <
                        (&(LENGTH a):int) - i +
                          (&(LENGTH b):int) - j) /\
                       ((&0:int) <= i + (&1:int) /\
                        i + (&1:int) <= (&(LENGTH a):int)) /\
                       ((&0:int) <= j + (&1:int) /\
                        j + (&1:int) <= (&(LENGTH b):int)) /\
                       c + (&1:int) +
                         (&(common_card
                             (suffix a (i + (&1:int)))
                             (suffix b (j + (&1:int)))):int) =
                         (&(common_card a b):int))))
              (c = (&(common_card a b):int)))))`;;
