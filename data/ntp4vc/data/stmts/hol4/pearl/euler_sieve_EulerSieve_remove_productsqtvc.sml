(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/euler_sieve_EulerSieve_remove_productsqtvc: the signed 63-bit
  verification condition for removing products while preserving the Euler
  sieve's primality, marking, and successor invariants. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory integer_wordTheory listTheory wordsTheory;

val erp_to_num_def = Define `
  erp_to_num (z : int) = if z < 0 then 0 else Num z`;

val erp_get_def = Define `
  erp_get (d : 'a) (xs : 'a list) (i : int) =
    if erp_to_num i < LENGTH xs then EL (erp_to_num i) xs else d`;

val erp_update_def = Define `
  erp_update (xs : 'a list) (i : int) (x : 'a) =
    LUPDATE x (erp_to_num i) xs`;

val erp_in63_def = Define `
  erp_in63 (x : int) <=>
    (-4611686018427387904 : int) <= x /\
    x <= (4611686018427387903 : int)`;

val erp_tdiv_def = Define `
  erp_tdiv (x : int) (y : int) = x quot y`;

val erp_prime_nat_def = Define `
  erp_prime_nat (n : int) <=>
    (2 : int) <= n /\
    !d : int.
      (1 : int) <= d /\ (?q : int. n = d * q) ==>
      d = (1 : int) \/ d = n`;

val erp_inv_nexts_def = Define `
  erp_inv_nexts (nexts : int list) (n : int) <=>
    !i : int.
      (0 : int) <= i /\ i < n ==>
      i < erp_get (0 : int) nexts i /\
      erp_get (0 : int) nexts i <= n`;

val erp_all_eliminated_marked_def = Define `
  erp_all_eliminated_marked
    (marked : bool list) (nexts : int list) <=>
    LENGTH marked = LENGTH nexts /\
    !i : int.
      (0 : int) <= i /\ i < &(LENGTH marked) ==>
      !j : int.
        i < j /\ j < erp_get (0 : int) nexts i ==>
        erp_get F marked j = T`;

val erp_all_eliminated_marked_partial_def = Define `
  erp_all_eliminated_marked_partial
    (marked : bool list) (nexts : int list) (minimum : int) <=>
    LENGTH marked = LENGTH nexts /\
    !i : int.
      minimum <= i /\ i < &(LENGTH marked) ==>
      !j : int.
        i < j /\ j < erp_get (0 : int) nexts i ==>
        erp_get F marked j = T`;

val erp_not_marked_impl_next_not_marked_def = Define `
  erp_not_marked_impl_next_not_marked
    (marked : bool list) (nexts : int list) (n : int) <=>
    LENGTH marked = LENGTH nexts /\
    (2 : int) <= &(LENGTH marked) /\
    (2 : int) <= n /\
    !i : int.
      (2 : int) <= i /\
      i <= erp_tdiv (&(LENGTH marked) - (1 : int)) n ==>
      erp_get (0 : int) nexts i <=
        erp_tdiv (&(LENGTH marked) - (1 : int)) n ==>
      ~(erp_get F marked i = T) ==>
      ~(erp_get F marked (erp_get (0 : int) nexts i) = T)`;

val erp_is_copy_def = Define `
  erp_is_copy (marked : bool list) (marked_old : bool list) <=>
    LENGTH marked = LENGTH marked_old /\
    !i : int.
      (0 : int) <= i /\ i < &(LENGTH marked) ==>
      ~(erp_get F marked i = T) ==>
      ~(erp_get F marked_old i = T)`;

val erp_not_marked_impl_next_not_marked_partial_def = Define `
  erp_not_marked_impl_next_not_marked_partial
    (marked : bool list) (nexts : int list) (n : int) (p : int) <=>
    LENGTH marked = LENGTH nexts /\
    (2 : int) <= &(LENGTH marked) /\
    (2 : int) <= n /\
    p <= erp_tdiv (&(LENGTH marked) - (1 : int)) n /\
    !i : int.
      (2 : int) <= i /\ i < p ==>
      erp_get (0 : int) nexts i <=
        erp_tdiv (&(LENGTH marked) - (1 : int)) n ==>
      ~(erp_get F marked i = T) ==>
      ~(erp_get F marked (erp_get (0 : int) nexts i) = T)`;

val erp_all_primes_def = Define `
  erp_all_primes (marked : bool list) (n : int) <=>
    !i : int.
      (0 : int) <= i /\ i < n ==>
      (~(erp_get F marked i = T) <=> erp_prime_nat i)`;

val erp_all_multiples_marked_def = Define `
  erp_all_multiples_marked
    (marked : bool list) (i : int) (maximum : int) <=>
    ((2 : int) <= i /\ i < &(LENGTH marked)) /\
    !k : int.
      (2 : int) <= k /\ k < maximum ==>
      i * k < &(LENGTH marked) ==>
      erp_get F marked (i * k) = T`;

val erp_previously_marked_multiples_def = Define `
  erp_previously_marked_multiples (marked : bool list) (n : int) <=>
    !i : int.
      (2 : int) <= i /\ i < n ==>
      erp_all_multiples_marked marked i (&(LENGTH marked))`;

val erp_only_multiples_marked_def = Define `
  erp_only_multiples_marked (marked : bool list) (n : int) <=>
    !k : int.
      (2 : int) <= k /\ k < &(LENGTH marked) ==>
      erp_get F marked k = T ==>
      ?i j : int.
        ((2 : int) <= i /\ i < n) /\
        ((2 : int) <= j /\ j < &(LENGTH marked)) /\
        i * j = k`;

val erp_prime_multiples_marked_def = Define `
  erp_prime_multiples_marked
    (marked_old : bool list) (marked : bool list)
    (n : int) (maximum : int) <=>
    LENGTH marked_old = LENGTH marked /\
    (n < maximum /\ maximum <= &(LENGTH marked)) /\
    !i : int.
      n <= i /\ i < maximum ==>
      ~(erp_get F marked_old i = T) ==>
      n * i < &(LENGTH marked_old) ==>
      erp_get F marked (n * i) = T`;

val erp_inv_remove_products_def = Define `
  erp_inv_remove_products
    (nexts : int list) (marked : bool list) (n : int) <=>
    LENGTH nexts = LENGTH marked /\
    ~(erp_get F marked (2 : int) = T) /\
    erp_all_primes marked n /\
    erp_prime_nat n /\
    ~(erp_get F marked n = T) /\
    erp_inv_nexts nexts (&(LENGTH nexts))`;

val erp_state_invariant_def = Define `
  erp_state_invariant
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (self : 'state) <=>
    w2i (maxf self) < (4611686018427387903 : int) /\
    (3 : int) <= w2i (maxf self) /\
    LENGTH (nexts self) = LENGTH (marked self) /\
    &(LENGTH (marked self)) = w2i (maxf self) + (1 : int) /\
    erp_inv_nexts (nexts self) (&(LENGTH (nexts self))) /\
    erp_all_eliminated_marked (marked self) (nexts self) /\
    (!i : int.
       (3 : int) <= i /\ i <= w2i (maxf self) ==>
       i rem (2 : int) = (0 : int) ==>
       erp_get F (marked self) i = T) /\
    (!i : int.
       (3 : int) <= i /\ i < w2i (maxf self) - (1 : int) ==>
       i rem (2 : int) = (1 : int) ==>
       erp_get (0 : int) (nexts self) i rem (2 : int) = (1 : int) \/
       erp_get (0 : int) (nexts self) i =
         w2i (maxf self) + (1 : int)) /\
    erp_get (0 : int) (nexts self) (w2i (maxf self)) =
      w2i (maxf self) + (1 : int) /\
    ((w2i (maxf self) - (1 : int)) rem (2 : int) = (0 : int) ==>
     erp_get (0 : int) (nexts self)
       (w2i (maxf self) - (1 : int)) = w2i (maxf self)) /\
    ((w2i (maxf self) - (1 : int)) rem (2 : int) = (1 : int) ==>
     erp_get (0 : int) (nexts self)
       (w2i (maxf self) - (1 : int)) =
       w2i (maxf self) + (1 : int))`;

val erp_loop_invariant_def = Define `
  erp_loop_invariant
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (n : int) (max1 : int) (marked_old : bool list)
    (t : 'state) (p : int) (x : int) <=>
    ((n <= p /\ p <= max1) /\
     ((3 : int) <= n /\ n <= max1) /\
     p rem (2 : int) = (1 : int) /\
     (p <= x /\ x < erp_get (0 : int) (nexts t) p) /\
     erp_get (0 : int) (nexts t) x =
       erp_get (0 : int) (nexts t) p /\
     erp_get F (marked t) (n * n) = T) /\
    erp_inv_remove_products (nexts t) (marked t) n /\
    erp_previously_marked_multiples (marked t) n /\
    ~(erp_get F (marked t) p = T) /\
    erp_is_copy (marked t) marked_old /\
    erp_all_eliminated_marked_partial marked_old (nexts t) x /\
    erp_not_marked_impl_next_not_marked marked_old (nexts t) n /\
    erp_prime_multiples_marked
      marked_old (marked t) n (erp_get (0 : int) (nexts t) x) /\
    erp_not_marked_impl_next_not_marked_partial
      (marked t) (nexts t) n p /\
    erp_only_multiples_marked (marked t) (n + (1 : int))`;

val erp_final_state_def = Define `
  erp_final_state
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (n : int) (marked_old : bool list) (t : 'state) <=>
    erp_inv_remove_products (nexts t) (marked t) n /\
    erp_not_marked_impl_next_not_marked
      (marked t) (nexts t) (erp_get (0 : int) (nexts t) n) /\
    erp_is_copy (marked t) marked_old /\
    erp_previously_marked_multiples (marked t) n /\
    erp_prime_multiples_marked
      marked_old (marked t) n (&(LENGTH (marked t))) /\
    erp_only_multiples_marked (marked t) (n + (1 : int))`;

val erp_final_conclusion_def = Define `
  erp_final_conclusion
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (n : int) (t : 'state) <=>
    let nextn = erp_get (0 : int) (nexts t) n in
      erp_inv_remove_products (nexts t) (marked t) n /\
      erp_not_marked_impl_next_not_marked
        (marked t) (nexts t) nextn /\
      erp_previously_marked_multiples (marked t) nextn /\
      erp_only_multiples_marked (marked t) nextn`;

val erp_next_condition_def = Define `
  erp_next_condition
    (nexts : 'state -> int list)
    (maxf : 'state -> 63 word)
    (t : 'state) (p : int) (next : int) <=>
    ((3 : int) <= next /\ next <= w2i (maxf t) + (1 : int)) /\
    next = erp_get (0 : int) (nexts t) p /\
    (next rem (2 : int) = (1 : int) \/
     next = w2i (maxf t) + (1 : int))`;

val erp_o2_condition_def = Define `
  erp_o2_condition (maxv : int) (next : int) (o2 : bool) <=>
    if (0 : int) <= next then
      (2 : int) <= maxv /\
      o2 = (if next <= maxv then T else F)
    else
      o2 = F`;

val erp_next_update_facts_def = Define `
  erp_next_update_facts
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (t : 'state) (p : int) (o4 : int) <=>
    (((0 : int) <= p /\ p <= w2i (maxf t)) /\
     p < o4 /\ o4 <= w2i (maxf t) + (1 : int)) /\
    p rem (2 : int) = (1 : int) /\
    (!j : int.
       p < j /\ j < o4 ==>
       erp_get F (marked t) j = T) /\
    ~(erp_get F (marked t) p = T) /\
    (o4 rem (2 : int) = (1 : int) \/
     o4 = w2i (maxf t) + (1 : int))`;

val erp_updated_successor_branch_def = Define `
  erp_updated_successor_branch
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (next : int)
    (t3 : 'state) (o4 : int) <=>
    erp_next_update_facts marked maxf t3 p o4 /\
    !t4 : 'state.
      marked t4 = marked t3 /\ maxf t4 = maxf t3 ==>
      nexts t4 = erp_update (nexts t3) p o4 ==>
      ((0 : int) <=
         max1 - erp_get (0 : int) (nexts t2) p /\
       max1 - erp_get (0 : int) (nexts t4) p <
         max1 - erp_get (0 : int) (nexts t2) p) /\
      erp_loop_invariant
        nexts marked n max1 marked_old t4 p next`;

val erp_marked_next_branch_def = Define `
  erp_marked_next_branch
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (next : int) (t3 : 'state) <=>
    (((3 : int) <= next /\ next <= w2i (maxf t3)) /\
     next rem (2 : int) = (1 : int)) /\
    !o4 : 63 word.
      (((3 : int) <= w2i o4 /\
        w2i o4 <= w2i (maxf t3) + (1 : int)) /\
       w2i o4 = erp_get (0 : int) (nexts t3) next /\
       (w2i o4 rem (2 : int) = (1 : int) \/
        w2i o4 = w2i (maxf t3) + (1 : int))) ==>
      erp_updated_successor_branch
        nexts marked maxf n max1 marked_old
        t2 p next t3 (w2i o4)`;

val erp_unmarked_next_branch_def = Define `
  erp_unmarked_next_branch
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (t3 : 'state) (next : int) <=>
    ((0 : int) <= max1 - erp_get (0 : int) (nexts t2) p /\
     max1 - erp_get (0 : int) (nexts t3) next <
       max1 - erp_get (0 : int) (nexts t2) p) /\
    erp_loop_invariant
      nexts marked n max1 marked_old t3 next next`;

val erp_after_product_write_def = Define `
  erp_after_product_write
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (next : int) (t3 : 'state) <=>
    (((0 : int) <= next /\ next <= w2i (maxf t3)) /\
     next rem (2 : int) = (1 : int)) /\
    if erp_get F (marked t3) next = T then
      erp_marked_next_branch
        nexts marked maxf n max1 marked_old t2 p next t3
    else
      erp_unmarked_next_branch
        nexts marked n max1 marked_old t2 p t3 next`;

val erp_product_result_def = Define `
  erp_product_result
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (next : int) (prod : int) <=>
    (((0 : int) <= prod /\ prod <= w2i (maxf t2)) /\
     prod rem (2 : int) = (1 : int)) /\
    !t3 : 'state.
      nexts t3 = nexts t2 /\ maxf t3 = maxf t2 ==>
      marked t3 = erp_update (marked t2) prod T ==>
      erp_after_product_write
        nexts marked maxf n max1 marked_old t2 p next t3`;

val erp_product_path_def = Define `
  erp_product_path
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (next : int) <=>
    erp_in63 (n * next) /\
    !prod : 63 word.
      w2i prod = n * next ==>
      erp_product_result
        nexts marked maxf n max1 marked_old
        t2 p next (w2i prod)`;

val erp_loop_step_def = Define `
  erp_loop_step
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (d : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) (next : int) <=>
    !o2 : bool.
      erp_o2_condition (w2i (maxf t2)) next o2 ==>
      if o2 = T then
        if next <= d then
          erp_product_path
            nexts marked maxf n max1 marked_old t2 p next
        else
          erp_final_state nexts marked n marked_old t2
      else
        erp_final_state nexts marked n marked_old t2`;

val erp_loop_body_def = Define `
  erp_loop_body
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (d : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) (p : int) <=>
    (((3 : int) <= p /\ p <= w2i (maxf t2)) /\
     p rem (2 : int) = (1 : int)) /\
    !next : 63 word.
      erp_next_condition nexts maxf t2 p (w2i next) ==>
      erp_loop_step
        nexts marked maxf n d max1 marked_old t2 p (w2i next)`;

val erp_all_loop_obligations_def = Define `
  erp_all_loop_obligations
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (d : int) (max1 : int)
    (marked_old : bool list) (t1 : 'state) <=>
    !t2 : 'state.
      maxf t2 = maxf t1 ==>
      !p : 63 word. !x : int.
        erp_loop_invariant
          nexts marked n max1 marked_old t2 (w2i p) x ==>
        erp_loop_body
          nexts marked maxf n d max1 marked_old t2 (w2i p)`;

val erp_square_continuation_def = Define `
  erp_square_continuation
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t2 : 'state) <=>
    erp_loop_invariant
      nexts marked n max1 marked_old t2 n n /\
    !t3 : 'state.
      maxf t3 = maxf t2 ==>
      erp_final_state nexts marked n marked_old t3 ==>
      erp_final_conclusion nexts marked n t3`;

val erp_square_result_def = Define `
  erp_square_result
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t1 : 'state) (square : int) <=>
    (((0 : int) <= square /\ square <= w2i (maxf t1)) /\
     square rem (2 : int) = (1 : int)) /\
    !t2 : 'state.
      nexts t2 = nexts t1 /\ maxf t2 = maxf t1 ==>
      marked t2 = erp_update (marked t1) square T ==>
      erp_square_continuation
        nexts marked maxf n max1 marked_old t2`;

val erp_square_obligations_def = Define `
  erp_square_obligations
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (max1 : int) (marked_old : bool list)
    (t1 : 'state) <=>
    erp_in63 (n * n) /\
    !square : 63 word.
      w2i square = n * n ==>
      erp_square_result
        nexts marked maxf n max1 marked_old t1 (w2i square)`;

val erp_remove_products_result_def = Define `
  erp_remove_products_result
    (nexts : 'state -> int list)
    (marked : 'state -> bool list)
    (maxf : 'state -> 63 word)
    (n : int) (d : int) (t1 : 'state) <=>
    let max1 = w2i (maxf t1) in
    let marked_old = marked t1 in
      erp_all_loop_obligations
        nexts marked maxf n d max1 marked_old t1 /\
      erp_square_obligations
        nexts marked maxf n max1 marked_old t1`;

val euler_sieve_EulerSieve_remove_productsqtvc_statement =
  ``!nexts : 'state -> int list.
    !marked : 'state -> bool list.
    !maxf : 'state -> 63 word.
      (!self : 'state. erp_state_invariant nexts marked maxf self) ==>
      !n : 63 word. !t1 : 'state.
        (3 : int) <= w2i n ==>
        w2i n <= w2i (maxf t1) ==>
        w2i n * w2i n <= w2i (maxf t1) ==>
        erp_inv_remove_products (nexts t1) (marked t1) (w2i n) ==>
        erp_previously_marked_multiples (marked t1) (w2i n) ==>
        erp_only_multiples_marked (marked t1) (w2i n) ==>
        erp_not_marked_impl_next_not_marked
          (marked t1) (nexts t1) (w2i n) ==>
        (2 : int) <= w2i (maxf t1) ==>
        (~(w2i n = (0 : int)) /\
         erp_in63 (erp_tdiv (w2i (maxf t1)) (w2i n))) /\
        !d : 63 word.
          w2i d = erp_tdiv (w2i (maxf t1)) (w2i n) ==>
          erp_remove_products_result
            nexts marked maxf (w2i n) (w2i d) t1``;
