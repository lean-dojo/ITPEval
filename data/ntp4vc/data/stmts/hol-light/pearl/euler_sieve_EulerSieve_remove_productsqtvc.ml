(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieve_remove_productsqtvc: the signed 63-bit
  verification condition for removing products while preserving the Euler
  sieve's primality, marking, and successor invariants. This file contains no
  proof.
*)

needs "Library/words.ml";;

let erp_nth = new_definition
 `erp_nth (d:A) (a:A list) (i:int) =
    if a = [] then d
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else d`;;

let erp_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:A. erp_update_nat [] n x = []) /\
    (!h:A. !t:A list. !n:num. !x:A.
       erp_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (erp_update_nat t (PRE n) x))`;;

let erp_update = new_definition
 `erp_update (a:A list) (i:int) (x:A) =
    if i < (&0:int)
    then erp_update_nat a 0 x
    else erp_update_nat a (num_of_int i) x`;;

let erp_in63 = new_definition
 `erp_in63 (x:int) <=>
    --(&2 pow 62) <= x /\ x <= &2 pow 62 - (&1:int)`;;

let erp_tdiv = new_definition
 `erp_tdiv (x:int) (y:int) =
    int_sgn x * int_sgn y * (abs x div abs y)`;;

let erp_prime_nat = new_definition
 `erp_prime_nat (n:int) <=>
    (&2:int) <= n /\
    (!d:int.
       (&1:int) <= d /\ d divides n
       ==> d = (&1:int) \/ d = n)`;;

let erp_inv_nexts = new_definition
 `erp_inv_nexts (nexts:int list) (n:int) <=>
    !i:int.
      (&0:int) <= i /\ i < n
      ==> i < erp_nth (&0:int) nexts i /\
          erp_nth (&0:int) nexts i <= n`;;

let erp_all_eliminated_marked = new_definition
 `erp_all_eliminated_marked
    (marked:bool list) (nexts:int list) <=>
    LENGTH marked = LENGTH nexts /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH marked):int)
       ==> !j:int.
             i < j /\ j < erp_nth (&0:int) nexts i
             ==> erp_nth F marked j = T)`;;

let erp_all_eliminated_marked_partial = new_definition
 `erp_all_eliminated_marked_partial
    (marked:bool list) (nexts:int list) (minimum:int) <=>
    LENGTH marked = LENGTH nexts /\
    (!i:int.
       minimum <= i /\ i < (&(LENGTH marked):int)
       ==> !j:int.
             i < j /\ j < erp_nth (&0:int) nexts i
             ==> erp_nth F marked j = T)`;;

let erp_not_marked_impl_next_not_marked = new_definition
 `erp_not_marked_impl_next_not_marked
    (marked:bool list) (nexts:int list) (n:int) <=>
    LENGTH marked = LENGTH nexts /\
    (&2:int) <= (&(LENGTH marked):int) /\
    (&2:int) <= n /\
    (!i:int.
       (&2:int) <= i /\
       i <= erp_tdiv ((&(LENGTH marked):int) - (&1:int)) n
       ==> erp_nth (&0:int) nexts i <=
           erp_tdiv ((&(LENGTH marked):int) - (&1:int)) n
       ==> ~(erp_nth F marked i = T)
       ==> ~(erp_nth F marked (erp_nth (&0:int) nexts i) = T))`;;

let erp_is_copy = new_definition
 `erp_is_copy (marked:bool list) (marked_old:bool list) <=>
    LENGTH marked = LENGTH marked_old /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH marked):int)
       ==> ~(erp_nth F marked i = T)
       ==> ~(erp_nth F marked_old i = T))`;;

let erp_not_marked_impl_next_not_marked_partial = new_definition
 `erp_not_marked_impl_next_not_marked_partial
    (marked:bool list) (nexts:int list) (n:int) (p:int) <=>
    LENGTH marked = LENGTH nexts /\
    (&2:int) <= (&(LENGTH marked):int) /\
    (&2:int) <= n /\
    p <= erp_tdiv ((&(LENGTH marked):int) - (&1:int)) n /\
    (!i:int.
       (&2:int) <= i /\ i < p
       ==> erp_nth (&0:int) nexts i <=
           erp_tdiv ((&(LENGTH marked):int) - (&1:int)) n
       ==> ~(erp_nth F marked i = T)
       ==> ~(erp_nth F marked (erp_nth (&0:int) nexts i) = T))`;;

let erp_all_primes = new_definition
 `erp_all_primes (marked:bool list) (n:int) <=>
    !i:int.
      (&0:int) <= i /\ i < n
      ==> (~(erp_nth F marked i = T) <=> erp_prime_nat i)`;;

let erp_all_multiples_marked = new_definition
 `erp_all_multiples_marked
    (marked:bool list) (i:int) (maximum:int) <=>
    ((&2:int) <= i /\ i < (&(LENGTH marked):int)) /\
    (!k:int.
       (&2:int) <= k /\ k < maximum
       ==> i * k < (&(LENGTH marked):int)
       ==> erp_nth F marked (i * k) = T)`;;

let erp_previously_marked_multiples = new_definition
 `erp_previously_marked_multiples (marked:bool list) (n:int) <=>
    !i:int.
      (&2:int) <= i /\ i < n
      ==> erp_all_multiples_marked
            marked i (&(LENGTH marked):int)`;;

let erp_only_multiples_marked = new_definition
 `erp_only_multiples_marked (marked:bool list) (n:int) <=>
    !k:int.
      (&2:int) <= k /\ k < (&(LENGTH marked):int)
      ==> erp_nth F marked k = T
      ==> ?i j:int.
            ((&2:int) <= i /\ i < n) /\
            ((&2:int) <= j /\ j < (&(LENGTH marked):int)) /\
            i * j = k`;;

let erp_prime_multiples_marked = new_definition
 `erp_prime_multiples_marked
    (marked_old:bool list) (marked:bool list)
    (n:int) (maximum:int) <=>
    LENGTH marked_old = LENGTH marked /\
    (n < maximum /\ maximum <= (&(LENGTH marked):int)) /\
    (!i:int.
       n <= i /\ i < maximum
       ==> ~(erp_nth F marked_old i = T)
       ==> n * i < (&(LENGTH marked_old):int)
       ==> erp_nth F marked (n * i) = T)`;;

let erp_inv_remove_products = new_definition
 `erp_inv_remove_products
    (nexts:int list) (marked:bool list) (n:int) <=>
    LENGTH nexts = LENGTH marked /\
    ~(erp_nth F marked (&2:int) = T) /\
    erp_all_primes marked n /\
    erp_prime_nat n /\
    ~(erp_nth F marked n = T) /\
    erp_inv_nexts nexts (&(LENGTH nexts):int)`;;

let erp_state_invariant = new_definition
 `erp_state_invariant
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word) (self:A) <=>
    ival (maxf self) < &2 pow 62 - (&1:int) /\
    (&3:int) <= ival (maxf self) /\
    LENGTH (nexts self) = LENGTH (marked self) /\
    (&(LENGTH (marked self)):int) = ival (maxf self) + (&1:int) /\
    erp_inv_nexts (nexts self) (&(LENGTH (nexts self)):int) /\
    erp_all_eliminated_marked (marked self) (nexts self) /\
    (!i:int.
       (&3:int) <= i /\ i <= ival (maxf self)
       ==> i rem (&2:int) = (&0:int)
       ==> erp_nth F (marked self) i = T) /\
    (!i:int.
       (&3:int) <= i /\ i < ival (maxf self) - (&1:int)
       ==> i rem (&2:int) = (&1:int)
       ==> erp_nth (&0:int) (nexts self) i rem (&2:int) = (&1:int) \/
           erp_nth (&0:int) (nexts self) i =
             ival (maxf self) + (&1:int)) /\
    erp_nth (&0:int) (nexts self) (ival (maxf self)) =
      ival (maxf self) + (&1:int) /\
    ((ival (maxf self) - (&1:int)) rem (&2:int) = (&0:int)
     ==> erp_nth (&0:int) (nexts self)
           (ival (maxf self) - (&1:int)) = ival (maxf self)) /\
    ((ival (maxf self) - (&1:int)) rem (&2:int) = (&1:int)
     ==> erp_nth (&0:int) (nexts self)
           (ival (maxf self) - (&1:int)) =
         ival (maxf self) + (&1:int))`;;

let erp_loop_invariant = new_definition
 `erp_loop_invariant
    (nexts:A->int list) (marked:A->bool list)
    (n:int) (max1:int) (marked_old:bool list)
    (t:A) (p:int) (x:int) <=>
    ((n <= p /\ p <= max1) /\
     ((&3:int) <= n /\ n <= max1) /\
     p rem (&2:int) = (&1:int) /\
     (p <= x /\ x < erp_nth (&0:int) (nexts t) p) /\
     erp_nth (&0:int) (nexts t) x =
       erp_nth (&0:int) (nexts t) p /\
     erp_nth F (marked t) (n * n) = T) /\
    erp_inv_remove_products (nexts t) (marked t) n /\
    erp_previously_marked_multiples (marked t) n /\
    ~(erp_nth F (marked t) p = T) /\
    erp_is_copy (marked t) marked_old /\
    erp_all_eliminated_marked_partial marked_old (nexts t) x /\
    erp_not_marked_impl_next_not_marked marked_old (nexts t) n /\
    erp_prime_multiples_marked
      marked_old (marked t) n (erp_nth (&0:int) (nexts t) x) /\
    erp_not_marked_impl_next_not_marked_partial
      (marked t) (nexts t) n p /\
    erp_only_multiples_marked (marked t) (n + (&1:int))`;;

let erp_final_state = new_definition
 `erp_final_state
    (nexts:A->int list) (marked:A->bool list)
    (n:int) (marked_old:bool list) (t:A) <=>
    erp_inv_remove_products (nexts t) (marked t) n /\
    erp_not_marked_impl_next_not_marked
      (marked t) (nexts t) (erp_nth (&0:int) (nexts t) n) /\
    erp_is_copy (marked t) marked_old /\
    erp_previously_marked_multiples (marked t) n /\
    erp_prime_multiples_marked
      marked_old (marked t) n (&(LENGTH (marked t)):int) /\
    erp_only_multiples_marked (marked t) (n + (&1:int))`;;

let erp_final_conclusion = new_definition
 `erp_final_conclusion
    (nexts:A->int list) (marked:A->bool list) (n:int) (t:A) <=>
    let nextn = erp_nth (&0:int) (nexts t) n in
    erp_inv_remove_products (nexts t) (marked t) n /\
    erp_not_marked_impl_next_not_marked (marked t) (nexts t) nextn /\
    erp_previously_marked_multiples (marked t) nextn /\
    erp_only_multiples_marked (marked t) nextn`;;

let erp_next_condition = new_definition
 `erp_next_condition
    (nexts:A->int list) (maxf:A->(63)word)
    (t:A) (p:int) (next:int) <=>
    ((&3:int) <= next /\ next <= ival (maxf t) + (&1:int)) /\
    next = erp_nth (&0:int) (nexts t) p /\
    (next rem (&2:int) = (&1:int) \/
     next = ival (maxf t) + (&1:int))`;;

let erp_o2_condition = new_definition
 `erp_o2_condition (maxv:int) (next:int) (o2:bool) <=>
    if (&0:int) <= next then
      (&2:int) <= maxv /\
      o2 = (if next <= maxv then T else F)
    else o2 = F`;;

let erp_next_update_facts = new_definition
 `erp_next_update_facts
    (marked:A->bool list) (maxf:A->(63)word)
    (t:A) (p:int) (o4:int) <=>
    (((&0:int) <= p /\ p <= ival (maxf t)) /\
     p < o4 /\ o4 <= ival (maxf t) + (&1:int)) /\
    p rem (&2:int) = (&1:int) /\
    (!j:int.
       p < j /\ j < o4
       ==> erp_nth F (marked t) j = T) /\
    ~(erp_nth F (marked t) p = T) /\
    (o4 rem (&2:int) = (&1:int) \/
     o4 = ival (maxf t) + (&1:int))`;;

let erp_updated_successor_branch = new_definition
 `erp_updated_successor_branch
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (next:int) (t3:A) (o4:int) <=>
    erp_next_update_facts marked maxf t3 p o4 /\
    (!t4:A.
       marked t4 = marked t3 /\ maxf t4 = maxf t3
       ==> nexts t4 = erp_update (nexts t3) p o4
       ==> ((&0:int) <=
              max1 - erp_nth (&0:int) (nexts t2) p /\
            max1 - erp_nth (&0:int) (nexts t4) p <
              max1 - erp_nth (&0:int) (nexts t2) p) /\
           erp_loop_invariant
             nexts marked n max1 marked_old t4 p next)`;;

let erp_marked_next_branch = new_definition
 `erp_marked_next_branch
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (next:int) (t3:A) <=>
    (((&3:int) <= next /\ next <= ival (maxf t3)) /\
     next rem (&2:int) = (&1:int)) /\
    (!o4:(63)word.
       (((&3:int) <= ival o4 /\
         ival o4 <= ival (maxf t3) + (&1:int)) /\
        ival o4 = erp_nth (&0:int) (nexts t3) next /\
        (ival o4 rem (&2:int) = (&1:int) \/
         ival o4 = ival (maxf t3) + (&1:int)))
       ==> erp_updated_successor_branch
             nexts marked maxf n max1 marked_old
             t2 p next t3 (ival o4))`;;

let erp_unmarked_next_branch = new_definition
 `erp_unmarked_next_branch
    (nexts:A->int list) (marked:A->bool list)
    (n:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (t3:A) (next:int) <=>
    ((&0:int) <= max1 - erp_nth (&0:int) (nexts t2) p /\
     max1 - erp_nth (&0:int) (nexts t3) next <
       max1 - erp_nth (&0:int) (nexts t2) p) /\
    erp_loop_invariant
      nexts marked n max1 marked_old t3 next next`;;

let erp_after_product_write = new_definition
 `erp_after_product_write
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (next:int) (t3:A) <=>
    (((&0:int) <= next /\ next <= ival (maxf t3)) /\
     next rem (&2:int) = (&1:int)) /\
    (if erp_nth F (marked t3) next = T then
       erp_marked_next_branch
         nexts marked maxf n max1 marked_old t2 p next t3
     else
       erp_unmarked_next_branch
         nexts marked n max1 marked_old t2 p t3 next)`;;

let erp_product_result = new_definition
 `erp_product_result
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (next:int) (prod:int) <=>
    (((&0:int) <= prod /\ prod <= ival (maxf t2)) /\
     prod rem (&2:int) = (&1:int)) /\
    (!t3:A.
       nexts t3 = nexts t2 /\ maxf t3 = maxf t2
       ==> marked t3 = erp_update (marked t2) prod T
       ==> erp_after_product_write
             nexts marked maxf n max1 marked_old t2 p next t3)`;;

let erp_product_path = new_definition
 `erp_product_path
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (next:int) <=>
    erp_in63 (n * next) /\
    (!prod:(63)word.
       ival prod = n * next
       ==> erp_product_result
             nexts marked maxf n max1 marked_old
             t2 p next (ival prod))`;;

let erp_loop_step = new_definition
 `erp_loop_step
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (d:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) (next:int) <=>
    !o2:bool.
      erp_o2_condition (ival (maxf t2)) next o2
      ==> if o2 = T then
            if next <= d then
              erp_product_path
                nexts marked maxf n max1 marked_old t2 p next
            else erp_final_state nexts marked n marked_old t2
          else erp_final_state nexts marked n marked_old t2`;;

let erp_loop_body = new_definition
 `erp_loop_body
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (d:int) (max1:int) (marked_old:bool list)
    (t2:A) (p:int) <=>
    (((&3:int) <= p /\ p <= ival (maxf t2)) /\
     p rem (&2:int) = (&1:int)) /\
    (!next:(63)word.
       erp_next_condition nexts maxf t2 p (ival next)
       ==> erp_loop_step
             nexts marked maxf n d max1 marked_old
             t2 p (ival next))`;;

let erp_all_loop_obligations = new_definition
 `erp_all_loop_obligations
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (d:int) (max1:int) (marked_old:bool list) (t1:A) <=>
    !t2:A.
      maxf t2 = maxf t1
      ==> !p:(63)word. !x:int.
            erp_loop_invariant
              nexts marked n max1 marked_old t2 (ival p) x
            ==> erp_loop_body
                  nexts marked maxf n d max1 marked_old t2 (ival p)`;;

let erp_square_continuation = new_definition
 `erp_square_continuation
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list) (t2:A) <=>
    erp_loop_invariant
      nexts marked n max1 marked_old t2 n n /\
    (!t3:A.
       maxf t3 = maxf t2
       ==> erp_final_state nexts marked n marked_old t3
       ==> erp_final_conclusion nexts marked n t3)`;;

let erp_square_result = new_definition
 `erp_square_result
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list)
    (t1:A) (square:int) <=>
    (((&0:int) <= square /\ square <= ival (maxf t1)) /\
     square rem (&2:int) = (&1:int)) /\
    (!t2:A.
       nexts t2 = nexts t1 /\ maxf t2 = maxf t1
       ==> marked t2 = erp_update (marked t1) square T
       ==> erp_square_continuation
             nexts marked maxf n max1 marked_old t2)`;;

let erp_square_obligations = new_definition
 `erp_square_obligations
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (max1:int) (marked_old:bool list) (t1:A) <=>
    erp_in63 (n * n) /\
    (!square:(63)word.
       ival square = n * n
       ==> erp_square_result
             nexts marked maxf n max1 marked_old t1 (ival square))`;;

let erp_remove_products_result = new_definition
 `erp_remove_products_result
    (nexts:A->int list) (marked:A->bool list)
    (maxf:A->(63)word)
    (n:int) (d:int) (t1:A) <=>
    let max1 = ival (maxf t1) in
    let marked_old = marked t1 in
    erp_all_loop_obligations
      nexts marked maxf n d max1 marked_old t1 /\
    erp_square_obligations
      nexts marked maxf n max1 marked_old t1`;;

let statement =
 `!nexts:A->int list.
  !marked:A->bool list.
  !maxf:A->(63)word.
    (!self:A. erp_state_invariant nexts marked maxf self)
    ==>
    !n:(63)word. !t1:A.
      (&3:int) <= ival n
      ==> ival n <= ival (maxf t1)
      ==> ival n * ival n <= ival (maxf t1)
      ==> erp_inv_remove_products
            (nexts t1) (marked t1) (ival n)
      ==> erp_previously_marked_multiples (marked t1) (ival n)
      ==> erp_only_multiples_marked (marked t1) (ival n)
      ==> erp_not_marked_impl_next_not_marked
            (marked t1) (nexts t1) (ival n)
      ==> (&2:int) <= ival (maxf t1)
      ==> (~(ival n = (&0:int)) /\
           erp_in63 (erp_tdiv (ival (maxf t1)) (ival n))) /\
          (!d:(63)word.
             ival d = erp_tdiv (ival (maxf t1)) (ival n)
             ==> erp_remove_products_result
                   nexts marked maxf (ival n) (ival d) t1)`;;
