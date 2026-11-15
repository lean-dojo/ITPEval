;; Statement-only formalization of VERINA corpus artifact verina_basic_81,
;; catalog title "DivisionFunction": deterministic natural-number division
;; returns an integer remainder-quotient pair, using (x, 0) for a zero divisor
;; and Euclidean division otherwise. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The two Nat input domains remain explicit
;; in the final correctness proposition.

(defun verina-basic-81-division-function-precond (x y)
  (declare (ignore x y))
  t)

;; Lean Int x Int values are represented bijectively by ACL2 cons pairs whose
;; car and cdr range over all integers.

(defun verina-basic-81-int-pair-p (result)
  (and
   (consp result)
   (integerp (car result))
   (integerp (cdr result))))

;; These total helpers reproduce Lean Nat division and remainder. For a zero
;; divisor Lean returns quotient zero and remainder x; for positive natural
;; divisors ACL2 FLOOR and MOD are exactly the same Euclidean operations.

(defun verina-basic-81-nat-div (x y)
  (if (and
       (natp x)
       (natp y)
       (not (equal y 0)))
      (floor x y)
    0))

(defun verina-basic-81-nat-mod (x y)
  (if (and
       (natp x)
       (natp y))
      (if (equal y 0)
          x
        (mod x y))
    0))

;; This is the source divMod helper. Its returned pair is ordered as
;; (remainder, quotient), with both natural results embedded in the integers.

(defun verina-basic-81-div-mod (x y)
  (let ((q (verina-basic-81-nat-div x y))
        (r (verina-basic-81-nat-mod x y)))
    (cons r q)))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. The branch and helper call preserve the complete executable
;; source implementation.

(defun verina-basic-81-division-function (x y)
  (if (equal y 0)
      (cons x 0)
    (verina-basic-81-div-mod x y)))

;; This is the complete source postcondition. The first component R is the
;; remainder and the second component Q is the quotient. The two implications
;; preserve the source's separate zero- and nonzero-divisor contracts.

(defun verina-basic-81-division-function-postcond
    (x y result)
  (and
   (natp x)
   (natp y)
   (verina-basic-81-int-pair-p result)
   (let ((r (car result))
         (q (cdr result)))
     (and
      (implies
       (equal y 0)
       (and
        (equal r x)
        (equal q 0)))
      (implies
       (not (equal y 0))
       (and
        (equal (+ (* q y) r) x)
        (and
         (<= 0 r)
         (< r y))
        (<= 0 q)))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all natural inputs, assumes exactly the source True precondition, and
;; applies the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-81-division-function-spec-satisfied-statement
    ()
  (forall (x y)
    (implies
     (and
      (natp x)
      (natp y)
      (verina-basic-81-division-function-precond x y))
     (verina-basic-81-division-function-postcond
      x
      y
      (verina-basic-81-division-function x y)))))

(value-triple :itpeval-statement-checked)
:q
