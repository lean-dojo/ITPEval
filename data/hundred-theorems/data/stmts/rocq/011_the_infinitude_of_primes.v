(* (c) Copyright 2006-2016 Microsoft Corporation and Inria.                  *)
(* Distributed under the terms of CeCILL-B.                                  *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import choice fintype div bigop.

(******************************************************************************)
(* This file contains the definitions of:                                     *)
(*        prime p <=> p is a prime.                                           *)
(*       primes m == the sorted list of prime divisors of m > 1, else [::].   *)
(*    pfactor p e == the value p ^ e of a prime factor (p, e).                *)
(*    NumFactor f == print version of a prime factor, converting the prime    *)
(*                   component to a Num (which can print large values).       *)
(* prime_decomp m == the list of prime factors of m > 1, sorted by primes.    *)
(*       logn p m == the e such that (p ^ e) \in prime_decomp n, else 0.      *)
(*  trunc_log p m == the largest e such that p ^ e <= m, or 0 if p <= 1 or    *)
(*                   m is 0.                                                  *)
(*     up_log p m == the smallest e such that m <= p ^ e, or 0 if p <= 1      *)
(*         pdiv n == the smallest prime divisor of n > 1, else 1.             *)
(*     max_pdiv n == the largest prime divisor of n > 1, else 1.              *)
(*     divisors m == the sorted list of divisors of m > 0, else [::].         *)
(*      totient n == the Euler totient (#|{i < n | i and n coprime}|).        *)
(*       nat_pred == the type of explicit collective nat predicates.          *)
(*                := simpl_pred nat.                                          *)
(*    -> We allow the coercion nat >-> nat_pred, interpreting p as pred1 p.   *)
(*    -> We define a predType for nat_pred, enabling the notation p \in pi.   *)
(*    -> We don't have nat_pred >-> pred, which would imply nat >-> Funclass. *)
(*           pi^' == the complement of pi : nat_pred, i.e., the nat_pred such *)
(*                   that (p \in pi^') = (p \notin pi).                       *)
(*         \pi(n) == the set of prime divisors of n, i.e., the nat_pred such  *)
(*                   that (p \in \pi(n)) = (p \in primes n).                  *)
(*         \pi(A) == the set of primes of #|A|, with A a collective predicate *)
(*                   over a finite Type.                                      *)
(*    -> The notation \pi(A) is implemented with a collapsible Coercion. The  *)
(*       type of A must coerce to finpred_sort (e.g., by coercing to {set T}) *)
(*       and not merely implement the predType interface (as seq T does).     *)
(*    -> The expression #|A| will only appear in \pi(A) after simplification  *)
(*       collapses the coercion, so it is advisable to do so early on.        *)
(*     pi.-nat n <=> n > 0 and all prime divisors of n are in pi.             *)
(*          n`_pi == the pi-part of n -- the largest pi.-nat divisor of n.    *)
(*               := \prod_(0 <= p < n.+1 | p \in pi) p ^ logn p n.            *)
(*    -> The nat >-> nat_pred coercion lets us write p.-nat n and n`_p.       *)
(* In addition to the lemmas relevant to these definitions, this file also    *)
(* contains the dvdn_sum lemma, so that bigop.v doesn't depend on div.v.      *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "pi ^'" (format "pi ^'").
Reserved Notation "pi .-nat" (format "pi .-nat").

(* The complexity of any arithmetic operation with the Peano representation *)
(* is pretty dreadful, so using algorithms for "harder" problems such as    *)
(* factoring, that are geared for efficient arithmetic leads to dismal      *)
(* performance -- it takes a significant time, for instance, to compute the *)
(* divisors of just a two-digit number. On the other hand, for Peano        *)
(* integers, prime factoring (and testing) is linear-time with a small      *)
(* constant factor -- indeed, the same as converting in and out of a binary *)
(* representation. This is implemented by the code below, which is then     *)
(* used to give the "standard" definitions of prime, primes, and divisors,  *)
(* which can then be used casually in proofs with moderately-sized numeric  *)
(* values (indeed, the code here performs well for up to 6-digit numbers).  *)

Module Import PrimeDecompAux.

(* We start with faster mod-2 and 2-valuation functions. *)

Fixpoint edivn2 q r := if r is r'.+2 then edivn2 q.+1 r' else (q, r).

Lemma edivn2P n : edivn_spec n 2 (edivn2 0 n).
Proof.
Admitted.

Fixpoint elogn2 e q r {struct q} :=
  match q, r with
  | 0, _ | _, 0 => (e, q)
  | q'.+1, 1 => elogn2 e.+1 q' q'
  | q'.+1, r'.+2 => elogn2 e q' r'
  end.
Arguments elogn2 : simpl nomatch.

Variant elogn2_spec n : nat * nat -> Type :=
  Elogn2Spec e m of n = 2 ^ e * m.*2.+1 : elogn2_spec n (e, m).

Lemma elogn2P n : elogn2_spec n.
Proof.
Admitted.

Definition ifnz T n (x y : T) := if n is 0 then y else x.

Variant ifnz_spec T n (x y : T) : T -> Type :=
  | IfnzPos of n > 0 : ifnz_spec n x y x
  | IfnzZero of n = 0 : ifnz_spec n x y y.

Lemma ifnzP T n (x y : T) : ifnz_spec n x y (ifnz n x y).
Proof.
Admitted.

(* The list of divisors and the Euler function are computed directly from    *)
(* the decomposition, using a merge_sort variant sort of the divisor list.   *)

Definition add_divisors f divs :=
  let: (p, e) := f in
  let add1 divs' := merge leq (map (NatTrec.mul p) divs') divs in
  iter e add1 divs.

Import NatTrec.

Definition add_totient_factor f m := let: (p, e) := f in p.-1 * p ^ e.-1 * m.

Definition cons_pfactor (p e : nat) pd := ifnz e ((p, e) :: pd) pd.

Notation "p ^? e :: pd" := (cons_pfactor p e pd)
  (at level 30, e at level 30, pd at level 60) : nat_scope.

End PrimeDecompAux.

(* For pretty-printing. *)
Definition NumFactor (f : nat * nat) := ([Num of f.1], f.2).

Definition pfactor p e := p ^ e.

Section prime_decomp.

Import NatTrec.

Local Fixpoint prime_decomp_rec m k a b c e :=
  let p := k.*2.+1 in
  if a is a'.+1 then
    if b - (ifnz e 1 k - c) is b'.+1 then
      [rec m, k, a', b', ifnz c c.-1 (ifnz e p.-2 1), e] else
    if (b == 0) && (c == 0) then
      let b' := k + a' in [rec b'.*2.+3, k, a', b', k.-1, e.+1] else
    let bc' := ifnz e (ifnz b (k, 0) (edivn2 0 c)) (b, c) in
    p ^? e :: ifnz a' [rec m, k.+1, a'.-1, bc'.1 + a', bc'.2, 0] [:: (m, 1)]
  else if (b == 0) && (c == 0) then [:: (p, e.+2)] else p ^? e :: [:: (m, 1)]
where "[ 'rec' m , k , a , b , c , e ]" := (prime_decomp_rec m k a b c e).

Definition prime_decomp n :=
  let: (e2, m2) := elogn2 0 n.-1 n.-1 in
  if m2 < 2 then 2 ^? e2 :: 3 ^? m2 :: [::] else
  let: (a, bc) := edivn m2.-2 3 in
  let: (b, c) := edivn (2 - bc) 2 in
  2 ^? e2 :: [rec m2.*2.+1, 1, a, b, c, 0].

End prime_decomp.

Definition primes n := unzip1 (prime_decomp n).

Definition prime p := if prime_decomp p is [:: (_ , 1)] then true else false.

Definition nat_pred := simpl_pred nat.

Definition pi_arg := nat.
Coercion pi_arg_of_nat (n : nat) : pi_arg := n.
Coercion pi_arg_of_fin_pred T pT (A : @fin_pred_sort T pT) : pi_arg := #|A|.
Arguments pi_arg_of_nat n /.
Arguments pi_arg_of_fin_pred {T pT} A /.
Definition pi_of (n : pi_arg) : nat_pred := [pred p in primes n].

Notation "\pi ( n )" := (pi_of n) (format "\pi ( n )") : nat_scope.
Notation "\p 'i' ( A )" := \pi(#|A|) (format "\p 'i' ( A )") : nat_scope.

Definition pdiv n := head 1 (primes n).

Definition max_pdiv n := last 1 (primes n).

Definition divisors n := foldr add_divisors [:: 1] (prime_decomp n).

Definition totient n := foldr add_totient_factor (n > 0) (prime_decomp n).

(* Correctness of the decomposition algorithm. *)

Lemma prime_decomp_correct :
  let pd_val pd := \prod_(f <- pd) pfactor f.
Proof.
Admitted.

Lemma primePn n :
  reflect (n < 2 \/ exists2 d, 1 < d < n & d %| n) (~~ prime n).
Proof.
Admitted.

Lemma primeNsig n : ~~ prime n -> 2 <= n -> { d : nat | 1 < d < n & d %| n }.
Proof.
Admitted.

Lemma primeP p :
  reflect (p > 1 /\ forall d, d %| p -> xpred2 1 p d) (prime p).
Proof.
Admitted.

Lemma prime_nt_dvdP d p : prime p -> d != 1 -> reflect (d = p) (d %| p).
Proof.
Admitted.

Arguments primeP {p}.
Arguments primePn {n}.

Lemma prime_gt1 p : prime p -> 1 < p.
Proof.
Admitted.

Lemma prime_gt0 p : prime p -> 0 < p.
Proof.
Admitted.

#[global] Hint Resolve prime_gt1 prime_gt0 : core.

Lemma prod_prime_decomp n :
  n > 0 -> n = \prod_(f <- prime_decomp n) f.
Proof.
Admitted.

Lemma even_prime p : prime p -> p = 2 \/ odd p.
Proof.
Admitted.

Lemma prime_oddPn p : prime p -> reflect (p = 2) (~~ odd p).
Proof.
Admitted.

Lemma odd_prime_gt2 p : odd p -> prime p -> p > 2.
Proof.
Admitted.

Lemma mem_prime_decomp n p e :
  (p, e) \in prime_decomp n -> [/\ prime p, e > 0 & p ^ e %| n].
Proof.
Admitted.

Lemma prime_coprime p m : prime p -> coprime p m = ~~ (p %| m).
Proof.
Admitted.

Lemma dvdn_prime2 p q : prime p -> prime q -> (p %| q) = (p == q).
Proof.
Admitted.

Lemma Euclid_dvd1 p : prime p -> (p %| 1) = false.
Proof.
Admitted.

Lemma Euclid_dvdM m n p : prime p -> (p %| m * n) = (p %| m) || (p %| n).
Proof.
Admitted.

Lemma Euclid_dvd_prod (I : Type) (r : seq I) (P : pred I) (f : I -> nat) p :
  prime p ->
  (p %| \prod_(i <- r | P i) f i) = \big[orb/false]_(i <- r | P i) (p %| f i).
Proof.
Admitted.

Lemma Euclid_dvdX m n p : prime p -> (p %| m ^ n) = (p %| m) && (n > 0).
Proof.
Admitted.

Lemma mem_primes p n : (p \in primes n) = [&& prime p, n > 0 & p %| n].
Proof.
Admitted.

Lemma sorted_primes n : sorted ltn (primes n).
Proof.
Admitted.

Lemma all_prime_primes n : all prime (primes n).
Proof.
Admitted.

Lemma eq_primes m n : (primes m =i primes n) <-> (primes m = primes n).
Proof.
Admitted.

Lemma primes_uniq n : uniq (primes n).
Proof.
Admitted.

(* The smallest prime divisor *)

Lemma pi_pdiv n : (pdiv n \in \pi(n)) = (n > 1).
Proof.
Admitted.

Lemma pdiv_prime n : 1 < n -> prime (pdiv n).
Proof.
Admitted.

Lemma pdiv_dvd n : pdiv n %| n.
Proof.
Admitted.

Lemma pi_max_pdiv n : (max_pdiv n \in \pi(n)) = (n > 1).
Proof.
Admitted.

Lemma max_pdiv_prime n : n > 1 -> prime (max_pdiv n).
Proof.
Admitted.

Lemma max_pdiv_dvd n : max_pdiv n %| n.
Proof.
Admitted.

Lemma pdiv_leq n : 0 < n -> pdiv n <= n.
Proof.
Admitted.

Lemma max_pdiv_leq n : 0 < n -> max_pdiv n <= n.
Proof.
Admitted.

Lemma pdiv_gt0 n : 0 < pdiv n.
Proof.
Admitted.

Lemma max_pdiv_gt0 n : 0 < max_pdiv n.
Proof.
Admitted.
#[global] Hint Resolve pdiv_gt0 max_pdiv_gt0 : core.

Lemma pdiv_min_dvd m d : 1 < d -> d %| m -> pdiv m <= d.
Proof.
Admitted.

Lemma max_pdiv_max n p : p \in \pi(n) -> p <= max_pdiv n.
Proof.
Admitted.

Lemma ltn_pdiv2_prime n : 0 < n -> n < pdiv n ^ 2 -> prime n.
Proof.
Admitted.

Lemma primePns n :
  reflect (n < 2 \/ exists p, [/\ prime p, p ^ 2 <= n & p %| n]) (~~ prime n).
Proof.
Admitted.

Arguments primePns {n}.

Lemma pdivP n : n > 1 -> {p | prime p & p %| n}.
Proof.
Admitted.
 
Lemma primes_eq0 n : (primes n == [::]) = (n < 2).
Proof.
Admitted.

Lemma primesM m n p : m > 0 -> n > 0 ->
  (p \in primes (m * n)) = (p \in primes m) || (p \in primes n).
Proof.
Admitted.

Lemma primesX m n : n > 0 -> primes (m ^ n) = primes m.
Proof.
Admitted.

Lemma primes_prime p : prime p -> primes p = [:: p].
Proof.
Admitted.

Lemma coprime_has_primes m n :
  0 < m -> 0 < n -> coprime m n = ~~ has [in primes m] (primes n).
Proof.
Admitted.

Lemma pdiv_id p : prime p -> pdiv p = p.
Proof.
Admitted.

Lemma pdiv_pfactor p k : prime p -> pdiv (p ^ k.
Proof.
Admitted.

(* Primes are unbounded. *)

Lemma prime_above m : {p | m < p & prime p}.
Proof.
Admitted.

(* "prime" logarithms and p-parts. *)

Fixpoint logn_rec d m r :=
  match r, edivn m d with
  | r'.+1, (_.+1 as m', 0) => (logn_rec d m' r').+1
  | _, _ => 0
  end.

Definition logn p m := if prime p then logn_rec p m m else 0.

Lemma lognE p m :
  logn p m = if [&& prime p, 0 < m & p %| m] then (logn p (m %/ p)).
Proof.
Admitted.

Lemma logn_gt0 p n : (0 < logn p n) = (p \in primes n).
Proof.
Admitted.

Lemma ltn_log0 p n : n < p -> logn p n = 0.
Proof.
Admitted.

Lemma logn0 p : logn p 0 = 0.
Proof.
Admitted.

Lemma logn1 p : logn p 1 = 0.
Proof.
Admitted.

Lemma pfactor_gt0 p n : 0 < p ^ logn p n.
Proof.
Admitted.
#[global] Hint Resolve pfactor_gt0 : core.

Lemma pfactor_dvdn p n m : prime p -> m > 0 -> (p ^ n %| m) = (n <= logn p m).
Proof.
Admitted.

Lemma pfactor_dvdnn p n : p ^ logn p n %| n.
Proof.
Admitted.

Lemma logn_prime p q : prime q -> logn p q = (p == q).
Proof.
Admitted.

Lemma pfactor_coprime p n :
  prime p -> n > 0 -> {m | coprime p m & n = m * p ^ logn p n}.
Proof.
Admitted.

Lemma pfactorK p n : prime p -> logn p (p ^ n) = n.
Proof.
Admitted.

Lemma pfactorKpdiv p n : prime p -> logn (pdiv (p ^ n)) (p ^ n) = n.
Proof.
Admitted.

Lemma dvdn_leq_log p m n : 0 < n -> m %| n -> logn p m <= logn p n.
Proof.
Admitted.

Lemma ltn_logl p n : 0 < n -> logn p n < n.
Proof.
Admitted.

Lemma logn_Gauss p m n : coprime p m -> logn p (m * n) = logn p n.
Proof.
Admitted.

Lemma logn_coprime p m : coprime p m -> logn p m = 0.
Proof.
Admitted.

Lemma lognM p m n : 0 < m -> 0 < n -> logn p (m * n) = logn p m + logn p n.
Proof.
Admitted.

Lemma lognX p m n : logn p (m ^ n) = n * logn p m.
Proof.
Admitted.

Lemma logn_div p m n : m %| n -> logn p (n %/ m) = logn p n - logn p m.
Proof.
Admitted.

Lemma dvdn_pfactor p d n : prime p ->
  reflect (exists2 m, m <= n & d = p ^ m) (d %| p ^ n).
Proof.
Admitted.

Lemma prime_decompE n : prime_decomp n = [seq (p, logn p n) | p <- primes n].
Proof.
Admitted.

(* Some combinatorial formulae. *)

Lemma divn_count_dvd d n : n %/ d = \sum_(1 <= i < n.
Proof.
Admitted.

Lemma logn_count_dvd p n : prime p -> logn p n = \sum_(1 <= k < n) (p ^ k %| n).
Proof.
Admitted.

(* Truncated real log. *)

Definition trunc_log p n :=
  let fix loop n k :=
    if k is k'.+1 then if p <= n then (loop (n %/ p) k').+1 else 0 else 0
  in if p <= 1 then 0 else loop n n.

Lemma trunc_log0 p : trunc_log p 0 = 0.
Proof.
Admitted.

Lemma trunc_log1 p : trunc_log p 1 = 0.
Proof.
Admitted.

Lemma trunc_log_bounds p n :
  1 < p -> 0 < n -> let k := trunc_log p n in p ^ k <= n < p ^ k.
Proof.
Admitted.

Lemma trunc_logP p n : 1 < p -> 0 < n -> p ^ trunc_log p n <= n.
Proof.
Admitted.

Lemma trunc_log_ltn p n : 1 < p -> n < p ^ (trunc_log p n).
Proof.
Admitted.

Lemma trunc_log_max p k j : 1 < p -> p ^ j <= k -> j <= trunc_log p k.
Proof.
Admitted.

Lemma trunc_log_eq0 p n : (trunc_log p n == 0) = (p <= 1) || (n <= p.
Proof.
Admitted.

Lemma trunc_log_gt0 p n : (0 < trunc_log p n) = (1 < p) && (p.
Proof.
Admitted.

Lemma trunc_log0n n : trunc_log 0 n = 0.
Proof.
Admitted.

Lemma trunc_log1n n : trunc_log 1 n = 0.
Proof.
Admitted.

Lemma leq_trunc_log p m n : m <= n -> trunc_log p m <= trunc_log p n.
Proof.
Admitted.

Lemma trunc_log_eq p n k : 1 < p -> p ^ n <= k < p ^ n.
Proof.
Admitted.

Lemma trunc_lognn p : 1 < p -> trunc_log p p = 1.
Proof.
Admitted.

Lemma trunc_expnK p n : 1 < p -> trunc_log p (p ^ n) = n.
Proof.
Admitted.

Lemma trunc_logMp p n : 1 < p -> 0 < n ->
  trunc_log p (p * n) = (trunc_log p n).
Proof.
Admitted.

Lemma trunc_log2_double n : 0 < n -> trunc_log 2 n.
Proof.
Admitted.

Lemma trunc_log2S n : 1 < n -> trunc_log 2 n = (trunc_log 2 n.
Proof.
Admitted.

(* Truncated up real logarithm *)

Definition up_log p n :=
  if (p <= 1) then 0 else
  let v := trunc_log p n in if n <= p ^ v then v else v.+1.

Lemma up_log0 p : up_log p 0 = 0.
Proof.
Admitted.

Lemma up_log1 p : up_log p 1 = 0.
Proof.
Admitted.

Lemma up_log_eq0 p n : (up_log p n == 0) = (p <= 1) || (n <= 1).
Proof.
Admitted.

Lemma up_log_gt0 p n : (0 < up_log p n) = (1 < p) && (1 < n).
Proof.
Admitted.

Lemma up_log_bounds p n :
  1 < p -> 1 < n -> let k := up_log p n in p ^ k.
Proof.
Admitted.

Lemma up_logP p n : 1 < p -> n <= p ^ up_log p n.
Proof.
Admitted.

Lemma up_log_gtn p n : 1 < p -> 1 < n -> p ^ (up_log p n).
Proof.
Admitted.

Lemma up_log_min p k j : 1 < p -> k <= p ^ j -> up_log p k <= j.
Proof.
Admitted.

Lemma leq_up_log p m n : m <= n -> up_log p m <= up_log p n.
Proof.
Admitted.

Lemma up_log_eq p n k : 1 < p -> p ^ n < k <= p ^ n.
Proof.
Admitted.

Lemma up_lognn p : 1 < p -> up_log p p = 1.
Proof.
Admitted.

Lemma up_expnK p n : 1 < p -> up_log p (p ^ n) = n.
Proof.
Admitted.

Lemma up_logMp p n : 1 < p -> 0 < n -> up_log p (p * n) = (up_log p n).
Proof.
Admitted.

Lemma up_log2_double n : 0 < n -> up_log 2 n.
Proof.
Admitted.

Lemma up_log2S n : 0 < n -> up_log 2 n.
Proof.
Admitted.

Lemma up_log_trunc_log p n :
  1 < p -> 1 < n -> up_log p n = (trunc_log p n.
Proof.
Admitted.

Lemma trunc_log_up_log p n :
  1 < p -> 0 < n -> trunc_log p n = (up_log p n.
Proof.
Admitted.

(* pi- parts *)

(* Testing for membership in set of prime factors. *)

Canonical nat_pred_pred := Eval hnf in [predType of nat_pred].

Coercion nat_pred_of_nat (p : nat) : nat_pred := pred1 p.

Section NatPreds.

Variables (n : nat) (pi : nat_pred).

Definition negn : nat_pred := [predC pi].

Definition pnat : pred nat := fun m => (m > 0) && all [in pi] (primes m).

Definition partn := \prod_(0 <= p < n.+1 | p \in pi) p ^ logn p n.

End NatPreds.

Notation "pi ^'" := (negn pi) : nat_scope.

Notation "pi .-nat" := (pnat pi) : nat_scope.

Notation "n `_ pi" := (partn n pi) : nat_scope.

Section PnatTheory.

Implicit Types (n p : nat) (pi rho : nat_pred).

Lemma negnK pi : pi^'^' =i pi.
Proof.
Admitted.

Lemma eq_negn pi1 pi2 : pi1 =i pi2 -> pi1^' =i pi2^'.
Proof.
Admitted.

Lemma eq_piP m n : \pi(m) =i \pi(n) <-> \pi(m) = \pi(n).
Proof.
Admitted.

Lemma part_gt0 pi n : 0 < n`_pi.
Proof.
Admitted.
Hint Resolve part_gt0 : core.

Lemma sub_in_partn pi1 pi2 n :
  {in \pi(n), {subset pi1 <= pi2}} -> n`_pi1 %| n`_pi2.
Proof.
Admitted.

Lemma eq_in_partn pi1 pi2 n : {in \pi(n), pi1 =i pi2} -> n`_pi1 = n`_pi2.
Proof.
Admitted.

Lemma eq_partn pi1 pi2 n : pi1 =i pi2 -> n`_pi1 = n`_pi2.
Proof.
Admitted.

Lemma partnNK pi n : n`_pi^'^' = n`_pi.
Proof.
Admitted.

Lemma widen_partn m pi n :
  n <= m -> n`_pi = \prod_(0 <= p < m.
Proof.
Admitted.

Lemma eq_partn_from_log m n (pi : nat_pred) : 0 < m -> 0 < n ->
  {in pi, logn^~ m =1 logn^~ n} -> m`_pi = n`_pi.
Proof.
Admitted.

Lemma partn0 pi : 0`_pi = 1.
Proof.
Admitted.

Lemma partn1 pi : 1`_pi = 1.
Proof.
Admitted.

Lemma partnM pi m n : m > 0 -> n > 0 -> (m * n)`_pi = m`_pi * n`_pi.
Proof.
Admitted.

Lemma partnX pi m n : (m ^ n)`_pi = m`_pi ^ n.
Proof.
Admitted.

Lemma partn_dvd pi m n : n > 0 -> m %| n -> m`_pi %| n`_pi.
Proof.
Admitted.

Lemma p_part p n : n`_p = p ^ logn p n.
Proof.
Admitted.

Lemma p_part_eq1 p n : (n`_p == 1) = (p \notin \pi(n)).
Proof.
Admitted.

Lemma p_part_gt1 p n : (n`_p > 1) = (p \in \pi(n)).
Proof.
Admitted.

Lemma primes_part pi n : primes n`_pi = filter [in pi] (primes n).
Proof.
Admitted.

Lemma filter_pi_of n m : n < m -> filter \pi(n) (index_iota 0 m) = primes n.
Proof.
Admitted.

Lemma partn_pi n : n > 0 -> n`_\pi(n) = n.
Proof.
Admitted.

Lemma partnT n : n > 0 -> n`_predT = n.
Proof.
Admitted.

Lemma eqn_from_log m n : 0 < m -> 0 < n -> logn^~ m =1 logn^~ n -> m = n.
Proof.
Admitted.

Lemma partnC pi n : n > 0 -> n`_pi * n`_pi^' = n.
Proof.
Admitted.

Lemma dvdn_part pi n : n`_pi %| n.
Proof.
Admitted.

Lemma logn_part p m : logn p m`_p = logn p m.
Proof.
Admitted.

Lemma partn_lcm pi m n : m > 0 -> n > 0 -> (lcmn m n)`_pi = lcmn m`_pi n`_pi.
Proof.
Admitted.

Lemma partn_gcd pi m n : m > 0 -> n > 0 -> (gcdn m n)`_pi = gcdn m`_pi n`_pi.
Proof.
Admitted.

Lemma partn_biglcm (I : finType) (P : pred I) F pi :
    (forall i, P i -> F i > 0) ->
  (\big[lcmn/1%N]_(i | P i) F i)`_pi = \big[lcmn/1%N]_(i | P i) (F i)`_pi.
Proof.
Admitted.

Lemma partn_biggcd (I : finType) (P : pred I) F pi :
    #|SimplPred P| > 0 -> (forall i, P i -> F i > 0) ->
  (\big[gcdn/0]_(i | P i) F i)`_pi = \big[gcdn/0]_(i | P i) (F i)`_pi.
Proof.
Admitted.

Lemma logn_gcd p m n : 0 < m -> 0 < n ->
  logn p (gcdn m n) = minn (logn p m) (logn p n).
Proof.
Admitted.

Lemma logn_lcm p m n : 0 < m -> 0 < n ->
  logn p (lcmn m n) = maxn (logn p m) (logn p n).
Proof.
Admitted.

Lemma sub_in_pnat pi rho n :
  {in \pi(n), {subset pi <= rho}} -> pi.
Proof.
Admitted.

Lemma eq_in_pnat pi rho n : {in \pi(n), pi =i rho} -> pi.
Proof.
Admitted.

Lemma eq_pnat pi rho n : pi =i rho -> pi.
Proof.
Admitted.

Lemma pnatNK pi n : pi^'^'.
Proof.
Admitted.

Lemma pnatI pi rho n : [predI pi & rho].
Proof.
Admitted.

Lemma pnatM pi m n : pi.
Proof.
Admitted.

Lemma pnatX pi m n : pi.
Proof.
Admitted.

Lemma part_pnat pi n : pi.
Proof.
Admitted.

Lemma pnatE pi p : prime p -> pi.
Proof.
Admitted.

Lemma pnat_id p : prime p -> p.
Proof.
Admitted.

Lemma coprime_pi' m n : m > 0 -> n > 0 -> coprime m n = \pi(m)^'.
Proof.
Admitted.

Lemma pnat_pi n : n > 0 -> \pi(n).
Proof.
Admitted.

Lemma pi_of_dvd m n : m %| n -> n > 0 -> {subset \pi(m) <= \pi(n)}.
Proof.
Admitted.

Lemma pi_ofM m n : m > 0 -> n > 0 -> \pi(m * n) =i [predU \pi(m) & \pi(n)].
Proof.
Admitted.

Lemma pi_of_part pi n : n > 0 -> \pi(n`_pi) =i [predI \pi(n) & pi].
Proof.
Admitted.

Lemma pi_of_exp p n : n > 0 -> \pi(p ^ n) = \pi(p).
Proof.
Admitted.

Lemma pi_of_prime p : prime p -> \pi(p) =i (p : nat_pred).
Proof.
Admitted.

Lemma p'natEpi p n : n > 0 -> p^'.
Proof.
Admitted.

Lemma p'natE p n : prime p -> p^'.
Proof.
Admitted.

Lemma pnatPpi pi n p : pi.
Proof.
Admitted.

Lemma pnat_dvd m n pi : m %| n -> pi.
Proof.
Admitted.

Lemma pnat_div m n pi : m %| n -> pi.
Proof.
Admitted.

Lemma pnat_coprime pi m n : pi.
Proof.
Admitted.

Lemma p'nat_coprime pi m n : pi^'.
Proof.
Admitted.

Lemma sub_pnat_coprime pi rho m n :
  {subset rho <= pi^'} -> pi.
Proof.
Admitted.

Lemma coprime_partC pi m n : coprime m`_pi n`_pi^'.
Proof.
Admitted.

Lemma pnat_1 pi n : pi.
Proof.
Admitted.

Lemma part_pnat_id pi n : pi.
Proof.
Admitted.

Lemma part_p'nat pi n : pi^'.
Proof.
Admitted.

Lemma partn_eq1 pi n : n > 0 -> (n`_pi == 1) = pi^'.
Proof.
Admitted.

Lemma pnatP pi n :
  n > 0 -> reflect (forall p, prime p -> p %| n -> p \in pi) (pi.
Proof.
Admitted.

Lemma pi_pnat pi p n : p.
Proof.
Admitted.

Lemma p_natP p n : p.
Proof.
Admitted.

Lemma pi'_p'nat pi p n : pi^'.
Proof.
Admitted.

Lemma pi_p'nat p pi n : pi.
Proof.
Admitted.

Lemma partn_part pi rho n : {subset pi <= rho} -> n`_rho`_pi = n`_pi.
Proof.
Admitted.

Lemma partnI pi rho n : n`_[predI pi & rho] = n`_pi`_rho.
Proof.
Admitted.

Lemma odd_2'nat n : odd n = 2^'.
Proof.
Admitted.

End PnatTheory.
#[global] Hint Resolve part_gt0 : core.

(************************************)
(* Properties of the divisors list. *)
(************************************)

Lemma divisors_correct n : n > 0 ->
  [/\ uniq (divisors n), sorted leq (divisors n)
    & forall d, (d \in divisors n) = (d %| n)].
Proof.
Admitted.

Lemma sorted_divisors n : sorted leq (divisors n).
Proof.
Admitted.

Lemma divisors_uniq n : uniq (divisors n).
Proof.
Admitted.

Lemma sorted_divisors_ltn n : sorted ltn (divisors n).
Proof.
Admitted.

Lemma dvdn_divisors d m : 0 < m -> (d %| m) = (d \in divisors m).
Proof.
Admitted.

Lemma divisor1 n : 1 \in divisors n.
Proof.
Admitted.

Lemma divisors_id n : 0 < n -> n \in divisors n.
Proof.
Admitted.

(* Big sum / product lemmas*)

Lemma dvdn_sum d I r (K : pred I) F :
  (forall i, K i -> d %| F i) -> d %| \sum_(i <- r | K i) F i.
Proof.
Admitted.

Lemma dvdn_partP n m : 0 < n ->
  reflect (forall p, p \in \pi(n) -> n`_p %| m) (n %| m).
Proof.
Admitted.

Lemma modn_partP n a b : 0 < n ->
  reflect (forall p : nat, p \in \pi(n) -> a = b %[mod n`_p]) (a == b %[mod n]).
Proof.
Admitted.

(* The Euler totient function *)

Lemma totientE n :
  n > 0 -> totient n = \prod_(p <- primes n) (p.
Proof.
Admitted.

Lemma totient_gt0 n : (0 < totient n) = (0 < n).
Proof.
Admitted.

Lemma totient_pfactor p e :
  prime p -> e > 0 -> totient (p ^ e) = p.
Proof.
Admitted.

Lemma totient_prime p : prime p -> totient p = p.
Proof.
Admitted.

Lemma totient_coprime m n :
  coprime m n -> totient (m * n) = totient m * totient n.
Proof.
Admitted.

Lemma totient_count_coprime n : totient n = \sum_(0 <= d < n) coprime n d.
Proof.
Admitted.

Lemma totient_gt1 n : (totient n > 1) = (n > 2).
Proof.
Admitted.
