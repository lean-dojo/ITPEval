(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* 
   Proof of Wilson theorem
   The proof is as follows:
    (p-1)! = 1 * 2 ... * p-2 * p-1
    we have
      1 mod p = 1
      p -1 mod p = - 1
      and for a, 2 <= a <= p-2, there is an inverse b (ab mod p =1)
            such 2 <= b <= p-2 and a<>b
            so we can rearrange the product 2 ... * p-2 in pairs
            of an element and its inverse. This means that
             2 ... * p-2 (mod p) = 1*)
Require Export ZisMod.
Open Scope Z_scope.
 
Theorem Zis_mod_rel_prime_inverse:
 forall a p,
 1 < p ->
 rel_prime a p ->
  (exists b , ( 1 <= b <= p - 1 ) /\ (rel_prime b p /\ Zis_mod (a * b) 1 p) ).
Proof.
Admitted.
 
Theorem wilson: forall p, prime p ->  Zis_mod (Zfact (p - 1)) (- 1) p.
Proof.
Admitted.
Hint Unfold Zfact : core.
 
 
 

(*
   If n = 4  (p-1)! mod p = 2
   If n > 4 and p composite
         p = x (p/x)
           if x <> (p/x) then 
                        1 < x < p and 1 < p/x < p
                         so  
                        x and (p/x) appears in (p-1)!
                         so
                          p divides (p-1)!, (p-1)! mod p = 0
           if x = (p/x) then 
                        1 < x < p and 1 < 2x < p
                         so  
                        x and (2x) appears in (p-1)!
                         so
                         p divides 2x^2 so p divides (p-1)!, (p-1)! mod p = 0
 *)

Theorem wilson_converse:
 forall p, 1 < p -> Zis_mod (Zfact (p - 1)) (- 1) p ->  prime p.
Proof.
Admitted.
