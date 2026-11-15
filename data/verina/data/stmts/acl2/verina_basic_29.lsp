;; Statement-only formalization of VERINA corpus artifact verina_basic_29,
;; catalog title "removeElement": a deterministic integer-array operation
;; removes the element at a valid natural-number index and satisfies the
;; resulting size, prefix, and left-shift contract. This file contains no proof.

(in-package "ACL2")

;; ACL2 proper lists of integers represent exactly the finite Array Int inputs
;; and outputs.

(defun verina-basic-29-int-array-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (integerp (car s))
       (verina-basic-29-int-array-p (cdr s)))
    (equal s nil)))

;; This combines the source Nat binder for K with its valid-index precondition.

(defun verina-basic-29-remove-element-precond (s k)
  (and
   (natp k)
   (< k (len s))))

;; On the valid-index domain this structural recursion is exactly
;; Array.eraseIdx!, retaining the original order of every other element.

(defun verina-basic-29-erase-index (s k)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (if (zp k)
          (cdr s)
        (cons
         (car s)
         (verina-basic-29-erase-index
          (cdr s)
          (- k 1))))
    nil))

;; The proof-valued precondition argument is computationally irrelevant, so
;; the target implementation erases it and preserves the complete computation.

(defun verina-basic-29-remove-element (s k)
  (verina-basic-29-erase-index s k))

;; NFIX of an integer difference is Lean natural-number subtraction.

(defun verina-basic-29-nat-sub (left right)
  (if (and
       (natp left)
       (natp right))
      (nfix (- left right))
    0))

;; These finite scans are exactly the two source universal Nat quantifiers.
;; The first checks indices 0 through K-1. The second checks indices K through
;; RESULT.size-1 and compares each output entry with the next input entry.

(defun verina-basic-29-prefix-preserved-p
    (s result index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (nth index result)
      (nth index s))
     (verina-basic-29-prefix-preserved-p
      s
      result
      (+ index 1)
      (- remaining 1)))))

(defun verina-basic-29-suffix-shifted-p
    (s result index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (and
     (equal
      (nth index result)
      (nth (+ index 1) s))
     (verina-basic-29-suffix-shifted-p
      s
      result
      (+ index 1)
      (- remaining 1)))))

;; This is the full source postcondition, including the typed Array Int and Nat
;; binders. Under the size equation every indexed access in the finite scans is
;; in bounds, so ACL2 NTH agrees exactly with Lean Array.getElem!.

(defun verina-basic-29-remove-element-postcond
    (s k result)
  (and
   (verina-basic-29-int-array-p s)
   (natp k)
   (verina-basic-29-int-array-p result)
   (equal
    (len result)
    (verina-basic-29-nat-sub
     (len s)
     1))
   (verina-basic-29-prefix-preserved-p
    s
    result
    0
    k)
   (verina-basic-29-suffix-shifted-p
    s
    result
    k
    (verina-basic-29-nat-sub
     (len result)
     k))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the full Array Int and Nat domains, applies the source precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-29-remove-element-spec-satisfied-statement ()
  (forall (s k)
    (implies
     (and
      (verina-basic-29-int-array-p s)
      (natp k)
      (verina-basic-29-remove-element-precond
       s
       k))
     (verina-basic-29-remove-element-postcond
      s
      k
      (verina-basic-29-remove-element
       s
       k)))))

(value-triple :itpeval-statement-checked)
:q
