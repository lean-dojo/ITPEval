;; Statement-only formalization of VERINA corpus artifact verina_basic_49,
;; catalog title "findFirstOdd": a deterministic scan of a nonempty integer
;; array returns none when no entry is odd, or the least index containing an
;; odd integer. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-49-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-49-int-array-p (cdr a)))
    (equal a nil)))

;; With positive divisor two, ACL2 MOD and Lean Int.emod agree on every
;; integer, so this is exactly the source isOdd Boolean helper.

(defun verina-basic-49-is-odd (x)
  (not (equal (mod x 2) 0)))

(defun verina-basic-49-find-first-odd-precond (a)
  (< 0 (len a)))

;; Option Nat is represented by :none or the tagged dotted pair
;; (:some . index), keeping none distinct from every natural-number index.

(defun verina-basic-49-option-nat-p (result)
  (or
   (equal result :none)
   (and
    (consp result)
    (equal (car result) :some)
    (natp (cdr result)))))

;; REMAINING is the suffix whose first entry has zero-based source index
;; INDEX. Testing before recursion exactly reproduces List.find? over
;; a.toList.zipIdx followed by Option.map of the index projection.

(defun verina-basic-49-find-first-odd-loop
    (remaining index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (if (verina-basic-49-is-odd (car remaining))
          (cons :some index)
        (verina-basic-49-find-first-odd-loop
         (cdr remaining)
         (+ index 1)))
    :none))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. Starting with the full array at index zero preserves the exact
;; executable source computation.

(defun verina-basic-49-find-first-odd (a)
  (verina-basic-49-find-first-odd-loop a 0))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-49-nth-default-zero (index a)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; These predicates preserve the source postcondition's universal Nat
;; binders and their exact strict bounds.

(defun-sk verina-basic-49-no-odd-before-p (a bound)
  (forall (j)
    (implies
     (and
      (natp j)
      (< j bound))
     (not
      (verina-basic-49-is-odd
       (verina-basic-49-nth-default-zero j a))))))

(defun-sk verina-basic-49-no-odd-in-array-p (a)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (not
      (verina-basic-49-is-odd
       (verina-basic-49-nth-default-zero i a))))))

;; This is the complete source match on the Option Nat result. A present
;; index is in bounds, points to an odd entry, and has no earlier odd entry;
;; an absent result means that every array entry is not odd.

(defun verina-basic-49-find-first-odd-postcond
    (a result)
  (and
   (verina-basic-49-int-array-p a)
   (verina-basic-49-option-nat-p result)
   (if (equal result :none)
       (verina-basic-49-no-odd-in-array-p a)
     (let ((index (cdr result)))
       (and
        (< index (len a))
        (verina-basic-49-is-odd
         (verina-basic-49-nth-default-zero index a))
        (verina-basic-49-no-odd-before-p
         a
         index))))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, assumes exactly the source nonempty
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-49-find-first-odd-spec-satisfied-statement
    ()
  (forall (a)
    (implies
     (and
      (verina-basic-49-int-array-p a)
      (verina-basic-49-find-first-odd-precond a))
     (verina-basic-49-find-first-odd-postcond
      a
      (verina-basic-49-find-first-odd a)))))

(value-triple :itpeval-statement-checked)
:q
