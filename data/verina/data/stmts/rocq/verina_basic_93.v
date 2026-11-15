(* Statement-only formalization of VERINA corpus artifact verina_basic_93,
   catalog title "SwapBitvectors": executable XOR-based swapping of two
   8-bit unsigned values, together with its unconditional precondition,
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Bool.Bool.

Module VerinaBasic93.

Record uint8 : Type := mk_uint8 {
  bit0 : bool;
  bit1 : bool;
  bit2 : bool;
  bit3 : bool;
  bit4 : bool;
  bit5 : bool;
  bit6 : bool;
  bit7 : bool
}.

Definition uint8_xor (x y : uint8) : uint8 :=
  mk_uint8
    (xorb (bit0 x) (bit0 y))
    (xorb (bit1 x) (bit1 y))
    (xorb (bit2 x) (bit2 y))
    (xorb (bit3 x) (bit3 y))
    (xorb (bit4 x) (bit4 y))
    (xorb (bit5 x) (bit5 y))
    (xorb (bit6 x) (bit6 y))
    (xorb (bit7 x) (bit7 y)).

Definition SwapBitvectors_precond
    (_X _Y : uint8) : Prop :=
  True.

Definition SwapBitvectors
    (X Y : uint8)
    (_h_precond : SwapBitvectors_precond X Y) : uint8 * uint8 :=
  let temp := uint8_xor X Y in
  let newY := uint8_xor temp Y in
  let newX := uint8_xor temp newY in
  (newX, newY).

Definition SwapBitvectors_postcond
    (X Y : uint8)
    (result : uint8 * uint8)
    (_h_precond : SwapBitvectors_precond X Y) : Prop :=
  fst result = Y /\
  snd result = X /\
  (X <> Y -> fst result <> X /\ snd result <> Y).

Theorem SwapBitvectors_spec_satisfied
    (X Y : uint8)
    (h_precond : SwapBitvectors_precond X Y) :
  SwapBitvectors_postcond
    X Y (SwapBitvectors X Y h_precond) h_precond.
Admitted.

End VerinaBasic93.
