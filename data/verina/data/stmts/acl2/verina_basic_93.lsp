;; Statement-only formalization of VERINA corpus artifact verina_basic_93,
;; catalog title "SwapBitvectors": a deterministic three-XOR program swaps
;; two 8-bit unsigned integers and satisfies the complete swapped-pair
;; contract. This file contains no proof.

(in-package "ACL2")

;; Canonical integers in [0, 256) represent Lean UInt8 values bijectively.

(defun verina-basic-93-uint8-p (value)
  (and
   (integerp value)
   (<= 0 value)
   (< value 256)))

;; The source precondition is True.

(defun verina-basic-93-swap-bitvectors-precond (x y)
  (declare (ignore x y))
  t)

;; Modulo-256 integer XOR is exactly UInt8.xor on canonical UInt8 values.

(defun verina-basic-93-xor8 (left right)
  (mod (logxor left right) 256))

;; A Lean UInt8 x UInt8 value is represented bijectively by an ACL2 dotted
;; pair whose car and cdr are canonical UInt8 integers.

(defun verina-basic-93-uint8-pair-p (result)
  (and
   (consp result)
   (verina-basic-93-uint8-p (car result))
   (verina-basic-93-uint8-p (cdr result))))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. These LET* bindings preserve the source's exact three-XOR
;; sequence and return the resulting ordered pair.

(defun verina-basic-93-swap-bitvectors (x y)
  (let* ((temp
          (verina-basic-93-xor8 x y))
         (new-y
          (verina-basic-93-xor8 temp y))
         (new-x
          (verina-basic-93-xor8 temp new-y)))
    (cons new-x new-y)))

;; This is the complete source postcondition, including the final implication
;; asserting componentwise change when the original inputs differ.

(defun verina-basic-93-swap-bitvectors-postcond
    (x y result)
  (and
   (verina-basic-93-uint8-p x)
   (verina-basic-93-uint8-p y)
   (verina-basic-93-uint8-pair-p result)
   (equal (car result) y)
   (equal (cdr result) x)
   (implies
    (not (equal x y))
    (and
     (not (equal (car result) x))
     (not (equal (cdr result) y))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all UInt8 inputs, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-93-swap-bitvectors-spec-satisfied-statement
    ()
  (forall (x y)
    (implies
     (and
      (verina-basic-93-uint8-p x)
      (verina-basic-93-uint8-p y)
      (verina-basic-93-swap-bitvectors-precond
       x
       y))
     (verina-basic-93-swap-bitvectors-postcond
      x
      y
      (verina-basic-93-swap-bitvectors
       x
       y)))))

(value-triple :itpeval-statement-checked)
:q
