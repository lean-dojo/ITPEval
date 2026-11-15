;; Statement-only formalization of VERINA corpus artifact verina_basic_11,
;; "lastDigit": a deterministic natural-number program returns the remainder
;; modulo 10, with the result between 0 and 9 and equal to the input's last
;; decimal digit. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Nat binder domain is explicit in the
;; final correctness statement.

(defun verina-basic-11-last-digit-precond (n)
  (declare (ignore n))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. On natural inputs, ACL2 MOD is exactly the source computation n % 10.

(defun verina-basic-11-last-digit (n)
  (mod n 10))

;; Lean Nat subtraction is truncated at zero.

(defun verina-basic-11-nat-sub (left right)
  (nfix (- left right)))

(defun verina-basic-11-last-digit-postcond (n result)
  (and
   (natp n)
   (natp result)
   (and
    (<= 0 result)
    (< result 10))
   (and
    (equal
     (verina-basic-11-nat-sub (mod n 10) result)
     0)
    (equal
     (verina-basic-11-nat-sub result (mod n 10))
     0))))

;; This predicate is the unproved final correctness proposition. Its antecedent
;; preserves the Nat input domain and True precondition, and its conclusion
;; applies the complete postcondition to the exact executable result.

(defun verina-basic-11-last-digit-spec-satisfied-statement (n)
  (implies
   (and
    (natp n)
    (verina-basic-11-last-digit-precond n))
   (verina-basic-11-last-digit-postcond
    n
    (verina-basic-11-last-digit n))))

(value-triple :itpeval-statement-checked)
:q
