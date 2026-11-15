;; Statement-only formalization of VERINA corpus artifact verina_basic_3,
;; catalog title "isDivisibleBy11": a deterministic integer program returns
;; true exactly when its input is an integer multiple of 11. This file contains
;; no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domain remains explicit in
;; the final correctness statement.

(defun verina-basic-3-is-divisible-by-11-precond (n)
  (declare (ignore n))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. For integer inputs and positive divisor 11, ACL2 MOD is exactly Lean
;; Int remainder, and EQUAL produces the corresponding ACL2 Boolean.

(defun verina-basic-3-is-divisible-by-11 (n)
  (if (equal (mod n 11) 0)
      t
    nil))

(defun verina-basic-3-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; These predicates preserve the postcondition's internal Int quantifiers.

(defun-sk verina-basic-3-has-multiple-witness-p (n)
  (exists (k)
    (and
     (integerp k)
     (equal n (* 11 k)))))

(defun-sk verina-basic-3-has-no-multiple-witness-p (n)
  (forall (k)
    (implies
     (integerp k)
     (not (equal n (* 11 k))))))

(defun verina-basic-3-is-divisible-by-11-postcond
    (n result)
  (and
   (integerp n)
   (verina-basic-3-bool-p result)
   (implies
    result
    (verina-basic-3-has-multiple-witness-p n))
   (implies
    (not result)
    (verina-basic-3-has-no-multiple-witness-p n))))

;; This predicate is the unproved final correctness proposition. It preserves
;; the arbitrary Int input and True precondition, and applies both directions
;; of the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-3-is-divisible-by-11-spec-satisfied-statement
    ()
  (forall (n)
    (implies
     (and
      (integerp n)
      (verina-basic-3-is-divisible-by-11-precond n))
     (verina-basic-3-is-divisible-by-11-postcond
      n
      (verina-basic-3-is-divisible-by-11 n)))))

(value-triple :itpeval-statement-checked)
:q
