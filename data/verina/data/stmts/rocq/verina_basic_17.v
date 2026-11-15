(* Statement-only formalization of VERINA corpus artifact verina_basic_17,
   catalog title "toLowercase": an executable Unicode-scalar string program
   maps each ASCII uppercase character to the codepoint 32 positions later
   and leaves every other character unchanged, together with its trivial
   precondition, pointwise postcondition, and correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Inductive lean_trit : Type :=
| Trit0
| Trit1
| Trit2.

Inductive lean_bits3 : Type :=
| LeanBits3 : bool -> bool -> bool -> lean_bits3.

Inductive lean_bits4 : Type :=
| LeanBits4 : bool -> bool -> bool -> bool -> lean_bits4.

Inductive lean_bits5 : Type :=
| LeanBits5 : bool -> bool -> bool -> bool -> bool -> lean_bits5.

Inductive lean_byte : Type :=
| LeanByte :
    bool -> bool -> bool -> bool ->
    bool -> bool -> bool -> bool ->
    lean_byte.

Inductive lean_char : Type :=
| LeanBmpLow :
    lean_trit -> lean_trit -> lean_trit ->
    lean_bits3 -> lean_byte -> lean_char
| LeanBmpHigh :
    lean_bits5 -> lean_byte -> lean_char
| LeanSupplementary :
    lean_bits4 -> lean_byte -> lean_byte -> lean_char.

Definition lean_string := list lean_char.

Definition lean_bit_value (b : bool) : nat :=
  if b then 1 else 0.

Definition lean_trit_value (t : lean_trit) : nat :=
  match t with
  | Trit0 => 0
  | Trit1 => 1
  | Trit2 => 2
  end.

Definition lean_bits3_value (bits : lean_bits3) : nat :=
  match bits with
  | LeanBits3 b2 b1 b0 =>
      lean_bit_value b2 * 4 +
      lean_bit_value b1 * 2 +
      lean_bit_value b0
  end.

Definition lean_bits4_value (bits : lean_bits4) : nat :=
  match bits with
  | LeanBits4 b3 b2 b1 b0 =>
      lean_bit_value b3 * 8 +
      lean_bit_value b2 * 4 +
      lean_bit_value b1 * 2 +
      lean_bit_value b0
  end.

Definition lean_bits5_value (bits : lean_bits5) : nat :=
  match bits with
  | LeanBits5 b4 b3 b2 b1 b0 =>
      lean_bit_value b4 * 16 +
      lean_bit_value b3 * 8 +
      lean_bit_value b2 * 4 +
      lean_bit_value b1 * 2 +
      lean_bit_value b0
  end.

Definition lean_byte_value (byte : lean_byte) : nat :=
  match byte with
  | LeanByte b7 b6 b5 b4 b3 b2 b1 b0 =>
      lean_bit_value b7 * 128 +
      lean_bit_value b6 * 64 +
      lean_bit_value b5 * 32 +
      lean_bit_value b4 * 16 +
      lean_bit_value b3 * 8 +
      lean_bit_value b2 * 4 +
      lean_bit_value b1 * 2 +
      lean_bit_value b0
  end.

Definition lean_char_to_nat (c : lean_char) : nat :=
  match c with
  | LeanBmpLow t2 t1 t0 bits byte =>
      ((((lean_trit_value t2 * 3 + lean_trit_value t1) * 3 +
          lean_trit_value t0) * 8 +
         lean_bits3_value bits) * 256 +
       lean_byte_value byte)
  | LeanBmpHigh bits byte =>
      57344 + lean_bits5_value bits * 256 + lean_byte_value byte
  | LeanSupplementary bits high low =>
      65536 + lean_bits4_value bits * 65536 +
      lean_byte_value high * 256 + lean_byte_value low
  end.

Definition lean_trit_of_nat (n : nat) : lean_trit :=
  match Nat.modulo n 3 with
  | O => Trit0
  | S O => Trit1
  | _ => Trit2
  end.

Definition lean_bit_of_nat (n : nat) : bool :=
  Nat.eqb (Nat.modulo n 2) 1.

Definition lean_bits3_of_nat (n : nat) : lean_bits3 :=
  LeanBits3
    (lean_bit_of_nat (Nat.div n 4))
    (lean_bit_of_nat (Nat.div n 2))
    (lean_bit_of_nat n).

Definition lean_bits4_of_nat (n : nat) : lean_bits4 :=
  LeanBits4
    (lean_bit_of_nat (Nat.div n 8))
    (lean_bit_of_nat (Nat.div n 4))
    (lean_bit_of_nat (Nat.div n 2))
    (lean_bit_of_nat n).

Definition lean_bits5_of_nat (n : nat) : lean_bits5 :=
  LeanBits5
    (lean_bit_of_nat (Nat.div n 16))
    (lean_bit_of_nat (Nat.div n 8))
    (lean_bit_of_nat (Nat.div n 4))
    (lean_bit_of_nat (Nat.div n 2))
    (lean_bit_of_nat n).

Definition lean_byte_of_nat (n : nat) : lean_byte :=
  LeanByte
    (lean_bit_of_nat (Nat.div n 128))
    (lean_bit_of_nat (Nat.div n 64))
    (lean_bit_of_nat (Nat.div n 32))
    (lean_bit_of_nat (Nat.div n 16))
    (lean_bit_of_nat (Nat.div n 8))
    (lean_bit_of_nat (Nat.div n 4))
    (lean_bit_of_nat (Nat.div n 2))
    (lean_bit_of_nat n).

Definition lean_low_char_of_nat (n : nat) : lean_char :=
  let q := Nat.div n 2048 in
  LeanBmpLow
    (lean_trit_of_nat (Nat.div q 9))
    (lean_trit_of_nat (Nat.modulo (Nat.div q 3) 3))
    (lean_trit_of_nat (Nat.modulo q 3))
    (lean_bits3_of_nat (Nat.modulo (Nat.div n 256) 8))
    (lean_byte_of_nat (Nat.modulo n 256)).

Definition lean_char_of_nat (n : nat) : lean_char :=
  if Nat.ltb n 55296 then
    lean_low_char_of_nat n
  else if Nat.ltb n 57344 then
    lean_low_char_of_nat 0
  else if Nat.ltb n 65536 then
    let m := n - 57344 in
    LeanBmpHigh
      (lean_bits5_of_nat (Nat.div m 256))
      (lean_byte_of_nat (Nat.modulo m 256))
  else if Nat.ltb n 1114112 then
    let m := n - 65536 in
    LeanSupplementary
      (lean_bits4_of_nat (Nat.div m 65536))
      (lean_byte_of_nat (Nat.modulo (Nat.div m 256) 256))
      (lean_byte_of_nat (Nat.modulo m 256))
  else
    lean_low_char_of_nat 0.

Definition lean_null_char : lean_char :=
  lean_char_of_nat 0.

Definition isUpperCase (c : lean_char) : bool :=
  andb
    (Nat.leb 65 (lean_char_to_nat c))
    (Nat.leb (lean_char_to_nat c) 90).

Definition shift32 (c : lean_char) : lean_char :=
  lean_char_of_nat (lean_char_to_nat c + 32).

Definition toLowercase_precond (_s : lean_string) : Prop :=
  True.

Definition toLowercase
    (s : lean_string)
    (_h_precond : toLowercase_precond s) : lean_string :=
  map
    (fun c => if isUpperCase c then shift32 c else c)
    s.

Definition toLowercase_postcond
    (s : lean_string)
    (result : lean_string)
    (_h_precond : toLowercase_precond s) : Prop :=
  length result = length s /\
  forall i : nat,
    i < length s ->
    (isUpperCase (nth i s lean_null_char) = true ->
      nth i result lean_null_char =
        shift32 (nth i s lean_null_char)) /\
    (isUpperCase (nth i s lean_null_char) = false ->
      nth i result lean_null_char =
        nth i s lean_null_char).

Theorem toLowercase_spec_satisfied
    (s : lean_string)
    (h_precond : toLowercase_precond s) :
  toLowercase_postcond
    s (toLowercase s h_precond) h_precond.
Admitted.
