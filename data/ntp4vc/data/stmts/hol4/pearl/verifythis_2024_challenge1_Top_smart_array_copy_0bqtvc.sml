(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2024_challenge1_Top_smart_array_copy_0bqtvc:
  the verification condition for copying an array in shuffled fixed-size
  subsegments followed by a final remainder chunk. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

val ntp4vc_smart_copy_to_num_def = Define `
  ntp4vc_smart_copy_to_num (i : int) =
    if i < (0 : int) then 0 else Num i`;

val ntp4vc_smart_copy_int_nth_def = Define `
  ntp4vc_smart_copy_int_nth (a : int list) (i : int) =
    if ntp4vc_smart_copy_to_num i < LENGTH a then
      EL (ntp4vc_smart_copy_to_num i) a
    else
      (0 : int)`;

val ntp4vc_smart_copy_nth_def = Define `
  ntp4vc_smart_copy_nth (a : 'a list) (i : int) =
    if ntp4vc_smart_copy_to_num i < LENGTH a then
      EL (ntp4vc_smart_copy_to_num i) a
    else
      ARB`;

val ntp4vc_smart_copy_permutation_def = Define `
  ntp4vc_smart_copy_permutation (l : int) (p : int list) <=>
    ((0 : int) <= l /\ l <= &(LENGTH p)) /\
    (!i : int.
       (0 : int) <= i /\ i < l ==>
       (0 : int) <= ntp4vc_smart_copy_int_nth p i /\
       ntp4vc_smart_copy_int_nth p i < l) /\
    (!i j : int.
       (0 : int) <= i /\ i < l ==>
       (0 : int) <= j /\ j < l ==>
       ~(i = j) ==>
       ~(ntp4vc_smart_copy_int_nth p i =
         ntp4vc_smart_copy_int_nth p j))`;

val ntp4vc_smart_copy_permutation_pair_def = Define `
  ntp4vc_smart_copy_permutation_pair
      (l : int) (p : int list) (invp : int list) <=>
    ntp4vc_smart_copy_permutation l p /\
    ntp4vc_smart_copy_permutation l invp /\
    (!i : int.
       (0 : int) <= i /\ i < l ==>
       ntp4vc_smart_copy_int_nth
         p (ntp4vc_smart_copy_int_nth invp i) = i) /\
    (!i : int.
       (0 : int) <= i /\ i < l ==>
       ntp4vc_smart_copy_int_nth
         invp (ntp4vc_smart_copy_int_nth p i) = i)`;

val ntp4vc_smart_copy_valid_chunk_def = Define `
  ntp4vc_smart_copy_valid_chunk
      (a : 'a list) (ofs : int) (len : int) <=>
    (0 : int) <= ofs /\
    ofs <= ofs + len /\
    ofs + len <= &(LENGTH a)`;

val ntp4vc_smart_copy_copy_def = Define `
  ntp4vc_smart_copy_copy
      (src : 'a list) (dst : 'a list) (ofs : int) (len : int) <=>
    ntp4vc_smart_copy_valid_chunk src ofs len /\
    LENGTH src = LENGTH dst /\
    (!i : int.
       ofs <= i /\ i < ofs + len ==>
       ntp4vc_smart_copy_nth dst i =
       ntp4vc_smart_copy_nth src i)`;

val ntp4vc_smart_copy_copy_to_def = Define `
  ntp4vc_smart_copy_copy_to
      (src : 'a list)
      (dst : 'a list)
      (ofss : int)
      (ofsd : int)
      (len : int) <=>
    ntp4vc_smart_copy_valid_chunk src ofss len /\
    ntp4vc_smart_copy_valid_chunk dst ofsd len /\
    LENGTH src = LENGTH dst /\
    (!i : int.
       (0 : int) <= i /\ i < len ==>
       ntp4vc_smart_copy_nth dst (ofsd + i) =
       ntp4vc_smart_copy_nth src (ofss + i)) /\
    (!i : int.
       ofsd <= i /\ i < ofsd + len ==>
       ntp4vc_smart_copy_nth dst i =
       ntp4vc_smart_copy_nth src (i + (ofss - ofsd)))`;

val verifythis_2024_challenge1_Top_smart_array_copy_0bqtvc_statement =
  ``!src : 'a list.
    !dst : 'a list.
    !k l q r : int.
      LENGTH src = LENGTH dst ==>
      (0 : int) < &(LENGTH dst) ==>
      (0 : int) < k ==>
      (0 : int) < l ==>
      (0 : int) <= q ==>
      (0 : int) <= r ==>
      r < k * l ==>
      &(LENGTH dst) = q * k * l + r ==>
      let m = k * l in
      let o1 = q - (1 : int) in
        (((0 : int) <= o1 + (1 : int) ==>
          ntp4vc_smart_copy_copy
            src dst (0 : int) ((0 : int) * m) /\
          (!dst1 : 'a list.
             LENGTH dst1 = LENGTH dst ==>
             (!s : int.
                (((0 : int) <= s /\ s <= o1) /\
                 ntp4vc_smart_copy_copy
                   src dst1 (0 : int) (s * m)) ==>
                let start = s * m in
                  (0 : int) < l /\
                  (!sigma invsigma : int list.
                     ((LENGTH sigma = LENGTH invsigma /\
                       &(LENGTH invsigma) = l) /\
                      ntp4vc_smart_copy_permutation_pair
                        l sigma invsigma) ==>
                     let o2 = l - (1 : int) in
                       (((0 : int) <= o2 + (1 : int) ==>
                         (ntp4vc_smart_copy_copy
                            src dst1 (0 : int) (s * m) /\
                          (!j' : int.
                             (0 : int) <= j' /\ j' < (0 : int) ==>
                             ntp4vc_smart_copy_copy
                               src
                               dst1
                               (start +
                                ntp4vc_smart_copy_int_nth sigma j' * k)
                               k)) /\
                         (!dst2 : 'a list.
                            LENGTH dst2 = LENGTH dst1 ==>
                            (!j : int.
                               (((0 : int) <= j /\ j <= o2) /\
                                ntp4vc_smart_copy_copy
                                  src dst2 (0 : int) (s * m) /\
                                (!j' : int.
                                   (0 : int) <= j' /\ j' < j ==>
                                   ntp4vc_smart_copy_copy
                                     src
                                     dst2
                                     (start +
                                      ntp4vc_smart_copy_int_nth sigma j' *
                                        k)
                                     k)) ==>
                               ((0 : int) <= j /\
                                j < &(LENGTH sigma)) /\
                               let startj =
                                 start +
                                 ntp4vc_smart_copy_int_nth sigma j * k
                               in
                                 (LENGTH src = LENGTH dst2 /\
                                  ntp4vc_smart_copy_valid_chunk
                                    src startj k /\
                                  ntp4vc_smart_copy_valid_chunk
                                    dst2 startj k) /\
                                 (!dst3 : 'a list.
                                    LENGTH dst3 = LENGTH dst2 ==>
                                    (ntp4vc_smart_copy_copy_to
                                       src dst3 startj startj k /\
                                     (!i : int.
                                        (0 : int) <= i /\ i < startj ==>
                                        ntp4vc_smart_copy_nth dst3 i =
                                        ntp4vc_smart_copy_nth dst2 i) /\
                                     (!i : int.
                                        startj + k <= i /\
                                        i < &(LENGTH dst3) ==>
                                        ntp4vc_smart_copy_nth dst3 i =
                                        ntp4vc_smart_copy_nth dst2 i)) ==>
                                    ntp4vc_smart_copy_copy
                                      src dst3 (0 : int) (s * m) /\
                                    (!j' : int.
                                       (0 : int) <= j' /\
                                       j' < j + (1 : int) ==>
                                       ntp4vc_smart_copy_copy
                                         src
                                         dst3
                                         (start +
                                          ntp4vc_smart_copy_int_nth
                                            sigma j' * k)
                                         k))) /\
                            ((ntp4vc_smart_copy_copy
                                src dst2 (0 : int) (s * m) /\
                              (!j' : int.
                                 (0 : int) <= j' /\
                                 j' < o2 + (1 : int) ==>
                                 ntp4vc_smart_copy_copy
                                   src
                                   dst2
                                   (start +
                                    ntp4vc_smart_copy_int_nth sigma j' * k)
                                   k)) ==>
                             ntp4vc_smart_copy_copy
                               src
                               dst2
                               (0 : int)
                               ((s + (1 : int)) * m)))) /\
                       (o2 + (1 : int) < (0 : int) ==>
                        ntp4vc_smart_copy_copy
                          src
                          dst1
                          (0 : int)
                          ((s + (1 : int)) * m))))) /\
          (ntp4vc_smart_copy_copy
             src dst1 (0 : int) ((o1 + (1 : int)) * m) ==>
           let last = q * m in
             (LENGTH src = LENGTH dst1 /\
              ntp4vc_smart_copy_valid_chunk src last r /\
              ntp4vc_smart_copy_valid_chunk dst1 last r) /\
             (!dst2 : 'a list.
                LENGTH dst2 = LENGTH dst1 ==>
                (ntp4vc_smart_copy_copy_to
                   src dst2 last last r /\
                 (!i : int.
                    (0 : int) <= i /\ i < last ==>
                    ntp4vc_smart_copy_nth dst2 i =
                    ntp4vc_smart_copy_nth dst1 i) /\
                 (!i : int.
                    last + r <= i /\ i < &(LENGTH dst2) ==>
                    ntp4vc_smart_copy_nth dst2 i =
                    ntp4vc_smart_copy_nth dst1 i)) ==>
                ntp4vc_smart_copy_copy
                  src dst2 (0 : int) (&(LENGTH dst)))))) /\
        (o1 + (1 : int) < (0 : int) ==>
         let last = q * m in
           (LENGTH src = LENGTH dst /\
            ntp4vc_smart_copy_valid_chunk src last r /\
            ntp4vc_smart_copy_valid_chunk dst last r) /\
           (!dst1 : 'a list.
              LENGTH dst1 = LENGTH dst ==>
              (ntp4vc_smart_copy_copy_to
                 src dst1 last last r /\
               (!i : int.
                  (0 : int) <= i /\ i < last ==>
                  ntp4vc_smart_copy_nth dst1 i =
                  ntp4vc_smart_copy_nth dst i) /\
               (!i : int.
                  last + r <= i /\ i < &(LENGTH dst1) ==>
                  ntp4vc_smart_copy_nth dst1 i =
                  ntp4vc_smart_copy_nth dst i)) ==>
              ntp4vc_smart_copy_copy
                src dst1 (0 : int) (&(LENGTH dst)))))``;
