Require Import ZArith Lia Znumtheory.
Require Import Natsets MyNat Ztools Zeqm Znumfacts.

(** Definition of the predicate : being the sum of four squares *)

Definition foursquare (n : Z) : Type :=
  {a : _ & { b: _ & { c : _ & { d |
    n = a * a + b * b + c * c + d * d
  }}}}.


(** Euler's identity and compatibility of the 4-square property wrt. multiplication *)

Lemma euler's_identity : forall a b c d w x y z : Z,
  let s z := z * z in
  (a * a + b * b + c * c + d * d) * (w * w + x * x + y * y + z * z) =
  s (a*w + b*x + c*y + d*z) +
  s (a*x - b*w - c*z + d*y) +
  s (a*y + b*z - c*w - d*x) +
  s (a*z - b*y + c*x - d*w).
Proof.
Admitted.

Lemma mult_foursquare_compat : forall n m : Z,
  foursquare n -> foursquare m -> foursquare (n * m)%Z.
Proof.
Admitted.

Lemma Zmod_sqrt_eq_compat : forall p i j, prime p ->
  (0 <= i -> 0 <= j -> 2 * i < p -> 2 * j < p ->
  i * i ≡ j * j [p] -> i = j)%Z.
Proof.
Admitted.

Lemma prime_odd : forall p, 2 <> p -> prime p -> p mod 2 = 1.
Proof.
Admitted.

Lemma odd_bound_1 : forall p i, p mod 2 = 1 -> i < Z.
Proof.
Admitted.


(** [modsym x m] is the unique y congruent to x such that -m/2≤x<m/2 *)

Definition modsym x m := (x + m / 2) mod m - m / 2.

Lemma modsym_bounds : forall x m, 0 < m -> - m <= 2 * modsym x m < m.
Proof.
Admitted.

Lemma modsym_mod_compat : forall x m, (modsym x m) mod m = x mod m.
Proof.
Admitted.

Lemma mod_modsym_compat : forall x m, modsym (x mod m) m = modsym x m.
Proof.
Admitted.

Lemma modsym_mod_diff : forall x m, 0 < m -> { k | modsym x m = x mod m + m * k }.
Proof.
Admitted.

Lemma modsym_eqm : forall x m, modsym x m ≡ x [ m ].
Proof.
Admitted.

Lemma prime_div_false : forall a p, prime p -> (a | p) -> 1 < a < p -> False.
Proof.
Admitted.

Lemma Zbounding_square : forall x m, 0 < m -> -m <= x <= m -> x ^ 2 <= m ^ 2.
Proof.
Admitted.


(** All prime numbers divides some [1+l²+m²] (plus convenient conditions on [l,m]) *)

Lemma prime_dividing_sum_of_two_squares_plus_one : forall p,
  prime p -> 3 <= p ->	
    {l : _ & {m : _ & { k |
      p * k = 1 + l * l + m * m /\
      2 * m < p /\  2 * l < p /\ 0 < k /\ 0 <= l /\ 0 <= m /\ (0 < l \/ 0 < m)}}}.
Proof.
Admitted.


(** Building bounds to prove things like x1²+x2²+x3²+x4²=m² /\ -m/2≤xi<m/2 => xi=-m/2 *)

Lemma egality_case_sum_of_four : forall a b c d M,
  a <= M -> b <= M -> c <= M -> d <= M ->
  a + b + c + d = 4 * M -> ((a = M) /\ (b = M)) /\ ((c = M) /\ (d = M)).
Proof.
Admitted.

Lemma square_bound_equality_case : forall a M,
  -M <= a < M -> M * M <= a * a -> a = - M.
Proof.
Admitted.

Lemma square_bound : forall x m, -m <= x <= m -> x * x <= m * m.
Proof.
Admitted.

Lemma square_bound_opp : forall x m, m <= x <= -m -> x * x <= m * m.
Proof.
Admitted.

Lemma egality_case_sum_of_four_squares : forall a b c d M,
  -M <= a < M -> -M <= b < M -> -M <= c < M -> -M <= d < M ->
  a * a + b * b + c * c + d * d = 4 * (M * M) ->
    ((a = -M) /\ (b = -M)) /\ ((c = -M) /\ (d = -M)).
Proof.
Admitted.


(** If [mp] is the sum of four squares, then so is [np] for a smaller [n] *)

Lemma foursquare_prime_factor_decreasing :
  forall p, prime p -> forall m, (1 < m /\ m < p)%Z ->
    foursquare (m * p) ->
      sigT (fun n => ((0 < n /\ n < m)%Z * foursquare (n * p))%type).
Proof.
Admitted.


(** Induction scheme to use the previous lemma *)
(* TODO déplacer ça ? *)
Definition lt_wf_rect :=
  fun p (P : nat -> Type) F =>
    well_founded_induction_type
      (well_founded_ltof nat (fun m => m)) P F p.


(** Using the previous lemma, one can decrease [mp] into [np] to eventually get [p] *)

Lemma foursquare_prime : forall p, prime p -> foursquare p.
Proof.
Admitted.


(** Trivial application of the previous lemma and euler's identity *)

Theorem lagrange_4_square_theorem : forall n, 0 <= n -> foursquare n.
Proof.
Admitted.


Definition lagrange_fun (n : Z) : (Z * Z) * (Z * Z) :=
  let (a, ha) := lagrange_4_square_theorem (Z.abs n) (Zabs_pos n) in
  let (b, hb) := ha in
  let (c, hc) := hb in
  let (d, _ ) := hc in
  ((a, b), (c, d)).

Lemma lagrange_fun_spec (n : Z) :
  (let (ab, cd) := lagrange_fun n in let (a, b) := ab in let (c, d) := cd in
  Z.
Proof.
Admitted.

(*
Require Extraction.
Extraction "Lagrange_four_square.ml" lagrange_fun.
*)

(*
Eval compute in lagrange_fun 0.

Print Opaque Dependencies lagrange_4_square_theorem.
*)
