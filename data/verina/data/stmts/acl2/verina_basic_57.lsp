;; Statement-only formalization of VERINA corpus artifact verina_basic_57,
;; catalog title "CountLessThan": a deterministic scan of an arbitrary integer
;; array returns the number of entries strictly below an integer threshold,
;; with correctness stated against an independent left fold. This file contains
;; no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-57-int-array-p (numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (consp numbers)
      (and
       (integerp (car numbers))
       (verina-basic-57-int-array-p (cdr numbers)))
    (equal numbers nil)))

;; The source precondition is True. The Array Int and Int binder domains remain
;; explicit in the final correctness proposition.

(defun verina-basic-57-count-less-than-precond
    (numbers threshold)
  (declare (ignore numbers threshold))
  t)

;; REMAINING is the suffix beginning at the source loop index. Testing its
;; head, updating the natural accumulator, and advancing to its tail exactly
;; reproduces the increasing-index local recursion while the index is in
;; bounds.

(defun verina-basic-57-count-loop
    (remaining threshold accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-57-count-loop
       (cdr remaining)
       threshold
       (if (< (car remaining) threshold)
           (+ accumulator 1)
         accumulator))
    accumulator))

;; The proof-valued True precondition argument is computationally irrelevant
;; and is erased. Starting with the full array and accumulator zero preserves
;; the exact executable CountLessThan computation.

(defun verina-basic-57-count-less-than
    (numbers threshold)
  (verina-basic-57-count-loop
   numbers
   threshold
   0))

;; This independent recursion is exactly the postcondition's Array.foldl with
;; the conditional increment function and initial accumulator zero.

(defun verina-basic-57-specification-fold
    (remaining threshold accumulator)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-57-specification-fold
       (cdr remaining)
       threshold
       (if (< (car remaining) threshold)
           (+ accumulator 1)
         accumulator))
    accumulator))

(defun verina-basic-57-fold-count
    (numbers threshold)
  (verina-basic-57-specification-fold
   numbers
   threshold
   0))

;; On natural-number arguments this is Lean Nat.sub, including truncation at
;; zero.

(defun verina-basic-57-nat-sub (left right)
  (if (and
       (natp left)
       (natp right))
      (nfix (- left right))
    0))

;; This is the complete source postcondition. It retains both truncated
;; subtraction equalities rather than replacing them by a single equality.
;; The explicit predicates preserve the Array Int, Int, and Nat binder types.

(defun verina-basic-57-count-less-than-postcond
    (numbers threshold result)
  (let ((expected
         (verina-basic-57-fold-count
          numbers
          threshold)))
    (and
     (verina-basic-57-int-array-p numbers)
     (integerp threshold)
     (natp result)
     (equal
      (verina-basic-57-nat-sub result expected)
      0)
     (equal
      (verina-basic-57-nat-sub expected result)
      0))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and integer threshold, assumes exactly the
;; source True precondition, and applies the complete postcondition to the
;; exact executable result.

(defun-sk
    verina-basic-57-count-less-than-spec-satisfied-statement
    ()
  (forall (numbers threshold)
    (implies
     (and
      (verina-basic-57-int-array-p numbers)
      (integerp threshold)
      (verina-basic-57-count-less-than-precond
       numbers
       threshold))
     (verina-basic-57-count-less-than-postcond
      numbers
      threshold
      (verina-basic-57-count-less-than
       numbers
       threshold)))))

(value-triple :itpeval-statement-checked)
:q
