;; Statement-only formalization of VERINA corpus artifact verina_basic_46,
;; catalog title "lastPosition": a deterministic scan of a nondecreasing
;; integer array returns the last index containing a specified integer, or
;; negative one when it is absent. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-46-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-46-int-array-p (cdr arr)))
    (equal arr nil)))

;; These two predicates are exactly List.Pairwise (fun x y => x <= y):
;; every head is at most every later entry, recursively for every suffix.

(defun verina-basic-46-head-at-most-all-p
    (head remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (<= head (car remaining))
       (verina-basic-46-head-at-most-all-p
        head
        (cdr remaining)))
    (equal remaining nil)))

(defun verina-basic-46-pairwise-nondecreasing-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (verina-basic-46-head-at-most-all-p
        (car arr)
        (cdr arr))
       (verina-basic-46-pairwise-nondecreasing-p
        (cdr arr)))
    (equal arr nil)))

(defun verina-basic-46-last-position-precond
    (arr elem)
  (declare (ignore elem))
  (verina-basic-46-pairwise-nondecreasing-p arr))

;; REMAINING is the suffix beginning at INDEX. At each entry this recursion
;; performs the source equality test, stores INDEX exactly when it matches,
;; and then advances to the next index. Exhausting the suffix returns the
;; latest stored index, initially negative one.

(defun verina-basic-46-last-position-loop
    (remaining elem index position)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (verina-basic-46-last-position-loop
       (cdr remaining)
       elem
       (+ index 1)
       (if (equal (car remaining) elem)
           index
         position))
    position))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. Starting at index zero and position negative one reproduces the
;; complete executable Lean implementation.

(defun verina-basic-46-last-position (arr elem)
  (verina-basic-46-last-position-loop
   arr
   elem
   0
   -1))

;; This recursion is List.drop on a natural count.

(defun verina-basic-46-drop (count values)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      values
    (if (consp values)
        (verina-basic-46-drop
         (- count 1)
         (cdr values))
      nil)))

;; This is List.all (fun value => value != elem).

(defun verina-basic-46-all-not-equal-p
    (values elem)
  (declare (xargs :measure (acl2-count values)))
  (if (consp values)
      (and
       (not (equal (car values) elem))
       (verina-basic-46-all-not-equal-p
        (cdr values)
        elem))
    (equal values nil)))

;; NFIX agrees with Lean Int.toNat on every integer.

(defun verina-basic-46-int-to-nat (value)
  (nfix value))

;; This is the complete source postcondition. It states the source result
;; sign disjunction; for a found result it checks the in-bounds matching entry
;; and absence of later matches; for negative one it checks absence everywhere.

(defun verina-basic-46-last-position-postcond
    (arr elem result)
  (and
   (verina-basic-46-int-array-p arr)
   (integerp elem)
   (integerp result)
   (or
    (equal result -1)
    (>= result 0))
   (implies
    (>= result 0)
    (let ((index
           (verina-basic-46-int-to-nat result)))
      (and
       (< index (len arr))
       (equal (nth index arr) elem)
       (verina-basic-46-all-not-equal-p
        (verina-basic-46-drop (+ index 1) arr)
        elem))))
   (implies
    (equal result -1)
    (verina-basic-46-all-not-equal-p arr elem))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array and integer element, assumes exactly the
;; source sortedness precondition, and applies the complete postcondition to
;; the exact executable result.

(defun-sk
    verina-basic-46-last-position-spec-satisfied-statement
    ()
  (forall (arr elem)
    (implies
     (and
      (verina-basic-46-int-array-p arr)
      (integerp elem)
      (verina-basic-46-last-position-precond
       arr
       elem))
     (verina-basic-46-last-position-postcond
      arr
      elem
      (verina-basic-46-last-position arr elem)))))

(value-triple :itpeval-statement-checked)
:q
