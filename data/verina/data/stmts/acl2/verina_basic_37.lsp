;; Statement-only formalization of VERINA corpus artifact verina_basic_37,
;; catalog title "findFirstOccurrence": a deterministic scan of a
;; nondecreasing integer array returns the first target index, or -1 when the
;; target is absent. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-37-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-37-int-array-p (cdr arr)))
    (equal arr nil)))

;; List.Pairwise (fun x y => x <= y) relates each head to every later
;; element, then recursively imposes the same condition on the tail.

(defun verina-basic-37-head-at-most-all-p (x xs)
  (declare (xargs :measure (acl2-count xs)))
  (if (consp xs)
      (and
       (<= x (car xs))
       (verina-basic-37-head-at-most-all-p
        x
        (cdr xs)))
    (equal xs nil)))

(defun verina-basic-37-pairwise-nondecreasing-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (verina-basic-37-head-at-most-all-p
        (car arr)
        (cdr arr))
       (verina-basic-37-pairwise-nondecreasing-p
        (cdr arr)))
    (equal arr nil)))

(defun verina-basic-37-find-first-occurrence-precond
    (arr target)
  (declare (ignore target))
  (verina-basic-37-pairwise-nondecreasing-p arr))

;; REMAINING is the suffix beginning at the source loop index INDEX. This
;; structural recursion preserves the source branch order: return INDEX on
;; equality, return -1 when the current entry exceeds TARGET, and otherwise
;; continue at the next index. Exhausting the array also returns -1.

(defun verina-basic-37-find-first-occurrence-loop
    (remaining target index)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((a (car remaining)))
        (if (equal a target)
            index
          (if (> a target)
              -1
            (verina-basic-37-find-first-occurrence-loop
             (cdr remaining)
             target
             (+ index 1)))))
    -1))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. Starting the exact loop at natural index zero reproduces the
;; executable Lean implementation.

(defun verina-basic-37-find-first-occurrence
    (arr target)
  (verina-basic-37-find-first-occurrence-loop
   arr
   target
   0))

;; Array.get! on Array Int returns the in-bounds entry and the inhabited
;; integer default zero outside the array.

(defun verina-basic-37-nth-default-zero
    (index arr)
  (if (and
       (natp index)
       (< index (len arr)))
      (nth index arr)
    0))

;; These predicates preserve the source postcondition's universal Nat
;; binders and their exact strict bounds.

(defun-sk verina-basic-37-no-target-before-p
    (arr target bound)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i bound))
     (not
      (equal
       (verina-basic-37-nth-default-zero i arr)
       target)))))

(defun-sk verina-basic-37-target-absent-p
    (arr target)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len arr)))
     (not
      (equal
       (verina-basic-37-nth-default-zero i arr)
       target)))))

;; This is the complete source postcondition. NFIX on an integer is Lean's
;; Int.toNat, and the proof-valued precondition argument is unused and erased.

(defun verina-basic-37-find-first-occurrence-postcond
    (arr target result)
  (and
   (verina-basic-37-int-array-p arr)
   (integerp target)
   (integerp result)
   (or
    (equal result -1)
    (<= 0 result))
   (implies
    (<= 0 result)
    (and
     (< (nfix result) (len arr))
     (equal
      (verina-basic-37-nth-default-zero
       (nfix result)
       arr)
      target)
     (verina-basic-37-no-target-before-p
      arr
      target
      (nfix result))))
   (implies
    (equal result -1)
    (verina-basic-37-target-absent-p
     arr
     target))))

;; This predicate is the unproved final correctness proposition. It
;; quantifies over the complete Array Int and Int domains, applies the exact
;; source precondition, and connects the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-37-find-first-occurrence-spec-satisfied-statement
    ()
  (forall (arr target)
    (implies
     (and
      (verina-basic-37-int-array-p arr)
      (integerp target)
      (verina-basic-37-find-first-occurrence-precond
       arr
       target))
     (verina-basic-37-find-first-occurrence-postcond
      arr
      target
      (verina-basic-37-find-first-occurrence
       arr
       target)))))

(value-triple :itpeval-statement-checked)
:q
