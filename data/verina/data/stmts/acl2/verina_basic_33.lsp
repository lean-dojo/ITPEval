;; Statement-only formalization of VERINA corpus artifact verina_basic_33,
;; catalog title "smallestMissingNumber": a deterministic scan of a
;; nondecreasing natural-number list returns its least missing natural number.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean List Nat values are represented bijectively by proper ACL2
;; lists whose elements are natural numbers.

(defun verina-basic-33-nat-listp (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (natp (car s))
       (verina-basic-33-nat-listp (cdr s)))
    (equal s nil)))

;; List.Pairwise (fun x y => x <= y) requires each head to be at most every
;; later element and recursively imposes the same condition on the tail.

(defun verina-basic-33-head-at-most-all-p (x s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (<= x (car s))
       (verina-basic-33-head-at-most-all-p
        x
        (cdr s)))
    (equal s nil)))

(defun verina-basic-33-pairwise-nondecreasing-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (verina-basic-33-head-at-most-all-p
        (car s)
        (cdr s))
       (verina-basic-33-pairwise-nondecreasing-p
        (cdr s)))
    (equal s nil)))

(defun verina-basic-33-smallest-missing-number-precond (s)
  (verina-basic-33-pairwise-nondecreasing-p s))

;; This is the source-local FINDMISSING recursion. It retains the source
;; branch order: return V at a larger head, increment V at an equal head, and
;; otherwise discard the smaller head without changing V.

(defun verina-basic-33-find-missing (v s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (let ((x (car s)))
        (if (> x v)
            v
          (if (equal x v)
              (verina-basic-33-find-missing
               (+ v 1)
               (cdr s))
            (verina-basic-33-find-missing
             v
             (cdr s)))))
    v))

;; The proof-valued precondition argument is computationally irrelevant and
;; erased. Starting the helper at zero exactly reproduces the executable Lean
;; implementation.

(defun verina-basic-33-smallest-missing-number (s)
  (verina-basic-33-find-missing 0 s))

;; For natural BOUND, this checks membership of BOUND - 1 down through zero,
;; exactly representing every natural K satisfying K < BOUND.

(defun verina-basic-33-all-below-present-p (bound s)
  (declare (xargs :measure (nfix bound)))
  (if (zp bound)
      t
    (and
     (member-equal (- bound 1) s)
     (verina-basic-33-all-below-present-p
      (- bound 1)
      s))))

;; This is the complete source postcondition: RESULT is absent, and every
;; smaller natural number occurs in the input list.

(defun verina-basic-33-smallest-missing-number-postcond
    (s result)
  (and
   (verina-basic-33-nat-listp s)
   (natp result)
   (not (member-equal result s))
   (verina-basic-33-all-below-present-p
    result
    s)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete List Nat domain, applies the exact source precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-33-smallest-missing-number-spec-satisfied-statement ()
  (forall (s)
    (implies
     (and
      (verina-basic-33-nat-listp s)
      (verina-basic-33-smallest-missing-number-precond s))
     (verina-basic-33-smallest-missing-number-postcond
      s
      (verina-basic-33-smallest-missing-number s)))))

(value-triple :itpeval-statement-checked)
:q
